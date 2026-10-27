module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21Abs
public import CFSG.Quasithin.Vol2.Ch1Quotient

public section

namespace CFSG.Quasithin.QA21

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Quasisimple

theorem eq_top_of_sup_eq_top {L : Type*} [Group L] (hq : CFSG.IsQuasisimple L) {K W : Subgroup L}
    (hK : ¬ Group.IsSolvable ↥K) (hW : W ≤ Subgroup.normalizer (K : Set L))
    (h : K ⊔ W ⊔ Subgroup.center L = ⊤) : K = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hq
  set Z : Subgroup L := Subgroup.center L with hZ
  set ρ : L →* L ⧸ Z := QuotientGroup.mk' Z with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective Z
  have hQn : (K ⊔ Z).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left : K ≤ K ⊔ Z).trans Subgroup.le_normalizer
    · intro w hw
      have h1 : w ∈ Subgroup.normalizer (K : Set L) ⊓ Subgroup.normalizer (Z : Set L) :=
        ⟨hW hw, by rw [Subgroup.normalizer_eq_top]; trivial⟩
      exact Subgroup.inf_normalizer_le_normalizer_sup K Z h1
    · exact (le_sup_right : Z ≤ K ⊔ Z).trans Subgroup.le_normalizer
  have hmap : (K ⊔ Z).map ρ = K.map ρ := by
    rw [Subgroup.map_sup]
    have : Z.map ρ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff z).2 hz
    rw [this, sup_bot_eq]
  have hKn : (K.map ρ).Normal := by
    rw [← hmap]
    exact hQn.map ρ hρs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map ρ) with hb | ht
  · exfalso
    apply hK
    have hKZ : K ≤ Z := by
      intro x hx
      have : ρ x ∈ K.map ρ := Subgroup.mem_map_of_mem ρ hx
      rw [hb, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKZ)
      (Subgroup.inclusion_injective hKZ)
  ·
    have hdec : ∀ x : L, ∃ k ∈ K, ∃ z ∈ Z, x = k * z := by
      intro x
      have : ρ x ∈ K.map ρ := by rw [ht]; trivial
      obtain ⟨k, hk, hkx⟩ := this
      refine ⟨k, hk, k⁻¹ * x, ?_, by group⟩
      have : ρ (k⁻¹ * x) = 1 := by rw [map_mul, map_inv, hkx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hcomm : commutator L ≤ K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨k, hk, z, hz, rfl⟩ := hdec x
      obtain ⟨k', hk', z', hz', rfl⟩ := hdec y
      have e : ⁅k * z, k' * z'⁆ = ⁅k, k'⁆ := by
        have hz1 : ∀ g : L, ⁅z, g⁆ = 1 := fun g =>
          commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz g).symm
        have hz2 : ∀ g : L, ⁅g, z'⁆ = 1 := fun g =>
          commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz' g)
        rw [commutatorElement_mul_left_eq_conj_mul, hz1, mul_one, mul_inv_cancel, one_mul,
          commutatorElement_mul_right_eq_mul_conj, hz2, mul_one, mul_inv_cancel_right]
      rw [e]
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
    rw [eq_top_iff]
    have : commutator L = ⊤ := hperf.commutator_eq_top
    rw [← this]
    exact hcomm

end Quasisimple

section Conj

variable {G : Type} [Group G]

@[expose] def conjOn (L : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    ↥L ≃* ↥L where
  toFun x := ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.1 hs x).1 x.2⟩
  invFun x := ⟨s⁻¹ * x * s, by
    have h := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (L : Set G)).inv_mem hs) x).1 x.2
    simpa using h⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def barConj (L : Subgroup G) (s : G)
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) (conjOn L s hs)
    (Subgroup.characteristic_iff_map_eq.1 inferInstance (conjOn L s hs))

theorem barConj_mk (L : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) :
    barConj L s hs (QuotientGroup.mk x) = QuotientGroup.mk (conjOn L s hs x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem map_conjOn_subgroupOf (L : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (L : Set G))
    {A : Subgroup G} (hA : s ∈ Subgroup.normalizer (A : Set G)) :
    (A.subgroupOf L).map (conjOn L s hs).toMonoidHom = A.subgroupOf L := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 hA x).1
      (Subgroup.mem_subgroupOf.1 hx))
  · intro x hx
    refine ⟨(conjOn L s hs).symm x, Subgroup.mem_subgroupOf.2 ?_,
      (conjOn L s hs).apply_symm_apply x⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hA)
      (x : G)).1 (Subgroup.mem_subgroupOf.1 hx)
    show s⁻¹ * (x : G) * s ∈ A
    simpa using h1

end Conj

section Main

variable {G : Type} [Group G]

theorem isSolvable_of_map_quotient_pCore {L : Type*} [Group L] [Finite L] (A : Subgroup L)
    (hA : Group.IsSolvable ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 L)))) :
    Group.IsSolvable ↥A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* L ⧸ CFSG.pCore 2 L := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
  set f₀ : ↥A →* L ⧸ CFSG.pCore 2 L := π.comp A.subtype with hf₀
  have hr : Group.IsSolvable ↥f₀.range := by
    have hle : f₀.range ≤ A.map π := by
      rintro _ ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hk : Group.IsSolvable ↥f₀.ker := by
    have hp : IsPGroup 2 ↥f₀.ker := by
      refine IsPGroup.of_injective (CFSG.pCore_isPGroup (p := 2) (G := L))
        ((A.subtype.comp f₀.ker.subtype).codRestrict (CFSG.pCore 2 L) fun x => ?_) ?_
      · exact (QuotientGroup.eq_one_iff _).1 x.2
      · intro x y hxy
        have h1 := congrArg (fun z : ↥(CFSG.pCore 2 L) => (z : L)) hxy
        exact Subtype.ext (Subtype.ext h1)
    have := hp.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range f₀.ker.subtype f₀.rangeRestrict (by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict] at hx
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem exists_parabolic_of_quotient [Finite G] {L K1 S D : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hcen : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L)
    (hK1L : K1 < L) (hK1 : ¬ Group.IsSolvable ↥K1)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hSK : S ≤ Subgroup.normalizer (K1 : Set G))
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hDL : D ≤ L) (hSD : S ⊓ L ≤ D)
    (hD : Group.IsSolvable ↥D)
    (hB : ∀ U : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), IsSylowTwoOf U ⊤ →
      ∃ P : Fin 2 → Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), BorelPkg _ U P) :
    ∃ P : Subgroup G, P < L ∧ K1 ≤ P ∧ D ≤ P ∧ S ⊓ L ≤ P ∧
      S ≤ Subgroup.normalizer (P : Set G) := by
  classical
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L with hN
  set π : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set K1L : Subgroup ↥L := K1.subgroupOf L with hK1L'
  set SL : Subgroup ↥L := (S ⊓ L).subgroupOf L with hSL'
  set DL : Subgroup ↥L := D.subgroupOf L with hDL'
  set U : Subgroup (↥L ⧸ N) := SL.map π with hU
  have hUsyl : IsSylowTwoOf U ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) π hπs
  obtain ⟨P, hP⟩ := hB U hUsyl
  set M : Subgroup (↥L ⧸ N) := (K1L ⊔ SL).map π with hM
  set D' : Subgroup (↥L ⧸ N) := DL.map π with hD'
  have hK1Lns : ¬ Group.IsSolvable ↥K1L := fun h =>
    hK1 (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hK1L.le).symm.toMonoidHom) (MulEquiv.injective _))
  have hUM : U ≤ M := Subgroup.map_mono le_sup_right
  have hMs : ¬ Group.IsSolvable ↥M := by
    intro h
    apply hK1Lns
    refine isSolvable_of_map_quotient_pCore K1L ?_
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (Subgroup.map_mono (le_sup_left : K1L ≤ K1L ⊔ SL) :
        K1L.map π ≤ M)) (Subgroup.inclusion_injective _)
  have hSKn : SL ≤ Subgroup.normalizer (K1L : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' : (x : G) ∈ S := (Subgroup.mem_subgroupOf.1 hx).1
    have := (Subgroup.mem_normalizer_iff.1 (hSK hx')) (h : G)
    simpa [K1L, Subgroup.mem_subgroupOf] using this
  have hM1 : M ≠ ⊤ := by
    intro hMt
    have h1 : K1L ⊔ SL ⊔ N = ⊤ := by
      have := Subgroup.comap_map_eq π (K1L ⊔ SL)
      rw [QuotientGroup.ker_mk', ← hM, hMt, Subgroup.comap_top] at this
      exact this.symm
    have h2 : K1L ⊔ SL ⊔ Subgroup.center ↥L = ⊤ := by
      rw [eq_top_iff, ← h1]
      exact sup_le_sup_left hcen _
    have h3 : K1L = ⊤ := eq_top_of_sup_eq_top hq hK1Lns hSKn h2
    refine not_le_of_gt hK1L fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ K1L := by rw [h3]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have hDLs : Group.IsSolvable ↥DL :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hDL).toMonoidHom) (MulEquiv.injective _)
  have hD's : Group.IsSolvable ↥D' :=
    Group.isSolvable_of_surjective (f := π.subgroupMap DL) (MonoidHom.subgroupMap_surjective _ _)
  have hSLD : SL ≤ DL := Subgroup.subgroupOf_mono L hSD
  have hUD : U ≤ D' := Subgroup.map_mono hSLD
  obtain ⟨j, hMj, hDj, hUj, hPj, hinv⟩ := hP.exists_index hUM hM1 hMs hUD hD's
  set Pg : Subgroup G := ((P j).comap π).map L.subtype with hPg
  have memPg : ∀ g : G, g ∈ Pg ↔ ∃ hg : g ∈ L, π ⟨g, hg⟩ ∈ P j := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  refine ⟨Pg, ?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun heq => hPj ?_
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hπs y
    have hx : (x : G) ∈ Pg := by rw [heq]; exact x.2
    obtain ⟨hg, h⟩ := (memPg x).1 hx
    exact h
  · intro k hk
    refine (memPg k).2 ⟨hK1L.le hk, hMj ?_⟩
    exact Subgroup.mem_map_of_mem π (le_sup_left (a := K1L) (b := SL)
      (Subgroup.mem_subgroupOf.2 hk))
  · intro d hd
    refine (memPg d).2 ⟨hDL hd, hDj ?_⟩
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hd)
  · intro x hx
    refine (memPg x).2 ⟨hx.2, hUj ?_⟩
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hx)
  · intro s hs
    have hsL : s ∈ Subgroup.normalizer (L : Set G) := hSL hs
    set α := barConj L s hsL with hα
    have hαπ : ∀ A : Subgroup ↥L, (A.map π).map α.toMonoidHom =
        (A.map (conjOn L s hsL).toMonoidHom).map π := by
      intro A
      have hcomp : α.toMonoidHom.comp π = π.comp (conjOn L s hsL).toMonoidHom := by
        ext x
        exact barConj_mk L s hsL x
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hsSL : s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hsL⟩
    have hSLeq : SL.map (conjOn L s hsL).toMonoidHom = SL :=
      map_conjOn_subgroupOf L s hsL hsSL
    have hK1Leq : K1L.map (conjOn L s hsL).toMonoidHom = K1L :=
      map_conjOn_subgroupOf L s hsL (hSK hs)
    have hαU : U.map α.toMonoidHom = U := by rw [hU, hαπ, hSLeq]
    have hαM : M.map α.toMonoidHom = M := by
      rw [hM, hαπ, Subgroup.map_sup, hSLeq, hK1Leq]
    have hPα : (P j).map α.toMonoidHom = P j := hinv α hαU hαM
    have hiff : ∀ x : ↥L, π (conjOn L s hsL x) ∈ P j ↔ π x ∈ P j := by
      intro x
      have hx : π (conjOn L s hsL x) = α (π x) := (barConj_mk L s hsL x).symm
      rw [hx]
      constructor
      · intro h
        rw [← hPα] at h
        obtain ⟨p, hp, hpx⟩ := h
        have : p = π x := α.injective hpx
        rwa [← this]
      · intro h
        rw [← hPα]
        exact ⟨π x, h, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhL : h ∈ L
    · have hsh : s * h * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hsL h).1 hhL
      constructor
      · intro hh
        obtain ⟨hg, h1⟩ := (memPg h).1 hh
        refine (memPg _).2 ⟨hsh, ?_⟩
        exact (hiff ⟨h, hhL⟩).2 h1
      · intro hh
        obtain ⟨hg, h1⟩ := (memPg _).1 hh
        refine (memPg h).2 ⟨hhL, ?_⟩
        exact (hiff ⟨h, hhL⟩).1 h1
    · have hsh : s * h * s⁻¹ ∉ L := fun hh =>
        hhL ((Subgroup.mem_normalizer_iff.1 hsL h).2 hh)
      constructor
      · intro hh
        exact absurd ((memPg h).1 hh).1 hhL
      · intro hh
        exact absurd ((memPg _).1 hh).1 hsh

end Main

end CFSG.Quasithin.QA21
