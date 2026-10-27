module

public import CFSG.Quasithin.Background.E6EighteenA
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.Quasithin.Background.E6TwentyTwoA

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Orders

@[expose] def IsA7Group (B : Type*) [Group B] : Prop :=
  Nonempty ((B ⧸ Subgroup.center B) ≃* alternatingGroup (Fin 7)) ∧
    (Nat.card (Subgroup.center B) = 1 ∨ Nat.card (Subgroup.center B) = 3)

@[expose] def HasA7Component (Q : Type*) [Group Q] : Prop :=
  ∃ B : Subgroup Q, CFSG.IsComponent B ∧ IsA7Group ↥B

theorem IsA7Group.of_mulEquiv {B B' : Type*} [Group B] [Group B'] (e : B ≃* B')
    (h : IsA7Group B) : IsA7Group B' := by
  obtain ⟨⟨φ⟩, hZ⟩ := h
  have hc := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
  refine ⟨⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩, ?_⟩
  have h1 : Nat.card (Subgroup.center B') = Nat.card (Subgroup.center B) := by
    rw [← hc]
    exact (Nat.card_congr ((Subgroup.center B).equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv).symm
  rwa [h1]

theorem HasA7Component.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : HasA7Component Q) : HasA7Component Q' := by
  obtain ⟨B, hB, h7⟩ := h
  exact ⟨B.map e.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv e hB,
    h7.of_mulEquiv (B.equivMapOfInjective e.toMonoidHom e.injective)⟩

@[expose] def NoA7Fix (S : Type*) [Group S] : Prop :=
  ∀ α : MulAut S, α * α = 1 → α ≠ 1 → ¬ HasA7Component ↥(Id2519.fixSubgroup α)

theorem NoA7Fix.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : NoA7Fix S) : NoA7Fix S' := by
  intro α' hα' hne hA
  set α : MulAut S := (MulAut.congr e).symm α' with hαdef
  have hα'eq : MulAut.congr e α = α' := by rw [hαdef, MulEquiv.apply_symm_apply]
  refine h α ?_ ?_ ?_
  · apply (MulAut.congr e).injective
    rw [map_mul, hα'eq, hα', map_one]
  · intro h1
    apply hne
    rw [← hα'eq, h1, map_one]
  · have hfix : ∀ y, α (e.symm y) = e.symm (α' y) := by
      intro y
      rw [← hα'eq]
      show α (e.symm y) = e.symm (e (α (e.symm y)))
      rw [MulEquiv.symm_apply_apply]
    have heq := Id2519.fixSubgroup_eq_map e.symm α' α hfix
    exact hA.of_mulEquiv (((Id2519.fixSubgroup α').equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).trans (MulEquiv.subgroupCongr heq.symm))

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at h
  have h7 : Nat.factorial 7 = 5040 := by decide
  omega

theorem IsA7Group.card_eq {B : Type*} [Group B] [Finite B] (h : IsA7Group B) :
    Nat.card B = Nat.card (Subgroup.center B) * 2520 := by
  obtain ⟨⟨φ⟩, -⟩ := h
  have h1 := (Subgroup.center B).card_mul_index
  rw [Subgroup.index_eq_card, Nat.card_congr φ.toEquiv, card_alternatingGroup_seven] at h1
  exact h1.symm

theorem IsA7Group.dvd_card {B : Type*} [Group B] [Finite B] (h : IsA7Group B) :
    2520 ∣ Nat.card B :=
  ⟨Nat.card (Subgroup.center B), by rw [h.card_eq, mul_comm]⟩

theorem IsA7Group.range {B Q : Type*} [Group B] [Group Q] [Finite B]
    (hq : CFSG.IsQuasisimple B) (h : IsA7Group B) (f : B →* Q) (hf : f.ker ≤ Subgroup.center B) :
    IsA7Group ↥f.range := by
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hker : f.rangeRestrict.ker ≤ Subgroup.center B := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hf
  have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hsurj hker
  have hB := h.card_eq
  obtain ⟨⟨φ⟩, hZ⟩ := h
  refine ⟨⟨e.symm.trans φ⟩, ?_⟩
  have hR : Nat.card ↥f.range = Nat.card (Subgroup.center ↥f.range) * 2520 := by
    have h1 := (Subgroup.center ↥f.range).card_mul_index
    rw [Subgroup.index_eq_card, Nat.card_congr (e.symm.trans φ).toEquiv,
      card_alternatingGroup_seven] at h1
    exact h1.symm
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card B := by
    rw [← Subgroup.index_ker f]
    exact f.ker.card_mul_index
  have h3 : Nat.card f.ker ∣ Nat.card (Subgroup.center B) := Subgroup.card_dvd_of_le hf
  have h4 : Nat.card (Subgroup.center ↥f.range) * Nat.card f.ker =
      Nat.card (Subgroup.center B) := by
    rw [hR, hB] at h1
    nlinarith
  have h5 : Nat.card (Subgroup.center ↥f.range) ∣ Nat.card (Subgroup.center B) :=
    ⟨Nat.card f.ker, h4.symm⟩
  rcases hZ with hz | hz
  · rw [hz] at h5
    exact Or.inl (Nat.dvd_one.1 h5)
  · rw [hz] at h5
    exact (Nat.dvd_prime Nat.prime_three).1 h5

end Orders


section Image

variable {Λ : Type*} [Group Λ]

theorem fix_conj_of_mk_fix {τ : MulAut Λ} {τb : MulAut (Λ ⧸ Subgroup.center Λ)}
    (hτ : ∀ x : Λ, τb (QuotientGroup.mk x) = QuotientGroup.mk (τ x)) {g d : Λ}
    (hg : τb (QuotientGroup.mk g) = QuotientGroup.mk g) (hd : τ d = d) :
    τ (g * d * g⁻¹) = g * d * g⁻¹ := by
  rw [hτ, QuotientGroup.eq] at hg
  have hcd := Subgroup.mem_center_iff.1 hg d
  rw [map_mul, map_mul, map_inv, hd]
  calc τ g * d * (τ g)⁻¹ = τ g * (d * ((τ g)⁻¹ * g)) * g⁻¹ := by group
    _ = τ g * (((τ g)⁻¹ * g) * d) * g⁻¹ := by rw [hcd]
    _ = g * d * g⁻¹ := by group

theorem map_fix_le {τ : MulAut Λ} {τb : MulAut (Λ ⧸ Subgroup.center Λ)}
    (hτ : ∀ x : Λ, τb (QuotientGroup.mk x) = QuotientGroup.mk (τ x)) :
    (Id2519.fixSubgroup τ).map (QuotientGroup.mk' (Subgroup.center Λ)) ≤
      Id2519.fixSubgroup τb := by
  rintro _ ⟨d, hd, rfl⟩
  have hd' : τ d = d := hd
  show τb (QuotientGroup.mk' (Subgroup.center Λ) d) = QuotientGroup.mk' (Subgroup.center Λ) d
  rw [QuotientGroup.mk'_apply, hτ, hd']

theorem map_fix_normal {τ : MulAut Λ} {τb : MulAut (Λ ⧸ Subgroup.center Λ)}
    (hτ : ∀ x : Λ, τb (QuotientGroup.mk x) = QuotientGroup.mk (τ x)) :
    (((Id2519.fixSubgroup τ).map (QuotientGroup.mk' (Subgroup.center Λ))).subgroupOf
      (Id2519.fixSubgroup τb)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (map_fix_le hτ)]
  have key : ∀ g ∈ Id2519.fixSubgroup τb,
      ∀ x ∈ (Id2519.fixSubgroup τ).map (QuotientGroup.mk' (Subgroup.center Λ)),
        g * x * g⁻¹ ∈ (Id2519.fixSubgroup τ).map (QuotientGroup.mk' (Subgroup.center Λ)) := by
    intro g hg x hx
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨g₀ * d * g₀⁻¹, fix_conj_of_mk_fix hτ hg hd, ?_⟩
    simp [QuotientGroup.mk'_apply]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using h

theorem isComponent_map_fix {τ : MulAut Λ} {τb : MulAut (Λ ⧸ Subgroup.center Λ)}
    (hτ : ∀ x : Λ, τb (QuotientGroup.mk x) = QuotientGroup.mk (τ x)) {B : Subgroup Λ}
    (hBF : B ≤ Id2519.fixSubgroup τ) (hq : CFSG.IsQuasisimple ↥B)
    (hsub : (B.subgroupOf (Id2519.fixSubgroup τ)).IsSubnormal) :
    CFSG.IsComponent ((B.map (QuotientGroup.mk' (Subgroup.center Λ))).subgroupOf
      (Id2519.fixSubgroup τb)) := by
  classical
  set π : Λ →* Λ ⧸ Subgroup.center Λ := QuotientGroup.mk' (Subgroup.center Λ) with hπ
  set D : Subgroup Λ := Id2519.fixSubgroup τ with hD
  set C : Subgroup (Λ ⧸ Subgroup.center Λ) := Id2519.fixSubgroup τb with hC
  have hDC : D.map π ≤ C := map_fix_le hτ
  have hKD' : B.map π ≤ D.map π := Subgroup.map_mono hBF
  have hKC : B.map π ≤ C := hKD'.trans hDC
  have hsub1 : ((B.map π).subgroupOf (D.map π)).IsSubnormal := by
    have h := Subgroup.IsSubnormal.map (MonoidHom.subgroupMap_surjective π D) hsub
    have heq : (B.subgroupOf D).map (π.subgroupMap D) = (B.map π).subgroupOf (D.map π) := by
      ext z
      constructor
      · rintro ⟨⟨d, hdD⟩, hdK, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr ⟨d, Subgroup.mem_subgroupOf.mp hdK, rfl⟩
      · intro hz
        obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
        exact ⟨⟨k, hBF hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
    rwa [heq] at h
  have hsub2 : ((B.map π).subgroupOf C).IsSubnormal := by
    have hnorm : ((D.map π).subgroupOf C).Normal := map_fix_normal hτ
    have hle : (B.map π).subgroupOf C ≤ (D.map π).subgroupOf C := fun x hx => hKD' hx
    have hsn : (((B.map π).subgroupOf C).subgroupOf ((D.map π).subgroupOf C)).IsSubnormal := by
      have h := hsub1.comap (Subgroup.subgroupOfEquivOfLe hDC).toMonoidHom
      convert h using 1
      ext x
      rfl
    exact Subgroup.IsSubnormal.trans hle hsn (Subgroup.Normal.isSubnormal hnorm)
  obtain ⟨k0, hk0K, hk0⟩ : ∃ k ∈ B, π k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have ha : (a₀ : Λ) ∈ Subgroup.center Λ := (QuotientGroup.eq_one_iff (a₀ : Λ)).1 (hcon a₀ a₀.2)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp ha b₀).symm
  have hqB : CFSG.IsQuasisimple ↥((B.map π).subgroupOf C) := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
      (φ := ((Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom).comp (π.subgroupMap B)) hq ?_ ?_
    · exact (Subgroup.subgroupOfEquivOfLe hKC).symm.surjective.comp
        (MonoidHom.subgroupMap_surjective π B)
    · refine ⟨⟨k0, hk0K⟩, fun h1 => hk0 ?_⟩
      have h2 := congrArg (fun z : ↥((B.map π).subgroupOf C) =>
        ((z : C) : Λ ⧸ Subgroup.center Λ)) h1
      exact h2
  exact ⟨hqB, hsub2⟩

end Image

section Ambient

variable {Y : Type} [Group Y] [Finite Y]

open Bar in
theorem hasA7Component_fix_barHom {K : Subgroup Y} (t : ↥(Subgroup.normalizer (K : Set Y)))
    {L : Subgroup Y} (hLc : IsComponentIn L (K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y)))
    (hL7 : IsA7Type L) : HasA7Component ↥(Id2519.fixSubgroup (barHom K t)) := by
  classical
  set τ : MulAut ↥K := conjL K t with hτdef
  have hτ : ∀ x : ↥K, barHom K t (QuotientGroup.mk x) = QuotientGroup.mk (τ x) := fun x =>
    barHom_mk t x (τ x) (conjL_apply t x)
  have hLK : L ≤ K := hLc.1.trans inf_le_left
  have hLt : L ≤ Subgroup.centralizer ({(t : Y)} : Set Y) := hLc.1.trans inf_le_right
  set B : Subgroup ↥K := L.subgroupOf K with hBdef
  have hfixeq : Id2519.fixSubgroup τ =
      (K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y)).subgroupOf K := by
    ext x
    rw [Id2519.mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      have h1 : (t : Y) * x * (t : Y)⁻¹ = x := by
        have := congrArg Subtype.val h
        rwa [hτdef, conjL_apply] at this
      calc (x : Y) * t = ((t : Y) * x * (t : Y)⁻¹) * t := by rw [h1]
        _ = t * x := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hτdef, conjL_apply, ← h]
      group
  have hBF : B ≤ Id2519.fixSubgroup τ := by
    rw [hfixeq]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hLt (Subgroup.mem_subgroupOf.mp hx)⟩
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hLc
  have hBq : CFSG.IsQuasisimple ↥B :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm hLq
  have hsub : (B.subgroupOf (Id2519.fixSubgroup τ)).IsSubnormal := by
    have h := hLc.2.2.comap (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y) ≤ K)).toMonoidHom
    have heq : B.subgroupOf (Id2519.fixSubgroup τ) =
        (L.subgroupOf (K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y))).comap
          ((Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ Subgroup.centralizer
            ({(t : Y)} : Set Y) ≤ K)).toMonoidHom.comp
            (MulEquiv.subgroupCongr hfixeq).toMonoidHom) := by
      ext x
      simp [hBdef, Subgroup.mem_subgroupOf]
    rw [heq]
    exact h.comap _
  have hcomp := isComponent_map_fix hτ hBF hBq hsub
  refine ⟨_, hcomp, ?_⟩
  set f : ↥L →* Qbar K := (QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hLK)
    with hfdef
  have hfker : f.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hl
    rw [Subgroup.mem_center_iff] at hl ⊢
    intro m
    apply Subtype.ext
    have := congrArg Subtype.val (hl (Subgroup.inclusion hLK m))
    simpa using this
  have h7 : IsA7Group ↥f.range := IsA7Group.range hLq hL7 f hfker
  have hrange : f.range = B.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hKC := (Subgroup.map_mono hBF).trans (map_fix_le hτ)
  exact h7.of_mulEquiv ((MulEquiv.subgroupCongr hrange).trans
    (Subgroup.subgroupOfEquivOfLe hKC).symm)

theorem eq_of_le_centralizer {K K₀ L P : Subgroup Y} {t : Y} (ht : t ∈ P)
    (hK₀ : IsComponentIn K₀ (K ⊓ Subgroup.centralizer ({t} : Set Y)))
    (hL : IsComponentIn L (K ⊓ Subgroup.centralizer (P : Set Y))) (hLK₀ : L ≤ K₀)
    (hPK₀ : P ≤ Subgroup.centralizer (K₀ : Set Y)) : L = K₀ := by
  have hK₀CP : K₀ ≤ K ⊓ Subgroup.centralizer (P : Set Y) :=
    le_inf (hK₀.1.trans inf_le_left) (Subgroup.le_centralizer_iff.1 hPK₀)
  have hK₀c : IsComponentIn K₀ (K ⊓ Subgroup.centralizer (P : Set Y)) :=
    BenderBranch.isComponentIn_of_le hK₀ hK₀CP
      (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 ht)))
  rcases BenderBranch.eq_or_commute_of_isComponentIn hL hK₀c with heq | hcomm
  · exact heq
  · exfalso
    have hLq := BenderBranch.isQuasisimple_of_isComponentIn hL
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
    have hbot : L = ⊥ := by
      rw [← hperf, eq_bot_iff, ← hcomm]
      exact Subgroup.commutator_mono le_rfl hLK₀
    exact (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial hLq) hbot

open Bar in
theorem exists_step_of_not_le (hI31 : AS_I_3_1_three) {H K P L : Subgroup Y}
    (hH : CFSG.SectionRank.IsSQTKCat ↥H) (hK : IsComponentIn K H) (hPH : P ≤ H)
    (hP : IsPGroup 2 P) (hPN : P ≤ Subgroup.normalizer (K : Set Y))
    (hL : IsComponentIn L (K ⊓ Subgroup.centralizer (P : Set Y))) (hL7 : IsA7Type L)
    (hPK : ¬ P ≤ Subgroup.centralizer (K : Set Y)) :
    ∃ t : ↥(Subgroup.normalizer (K : Set Y)), (t : Y) ∈ P ∧ barHom K t * barHom K t = 1 ∧
      barHom K t ≠ 1 ∧ ∃ K₀ : Subgroup Y, L ≤ K₀ ∧
        IsComponentIn K₀ (K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y)) ∧
        P ≤ Subgroup.normalizer (K₀ : Set Y) ∧
        IsComponentIn K₀ ((K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y)) ⊔ P) ∧
        IsComponentIn L (K₀ ⊓ Subgroup.centralizer (P : Set Y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hperf : Group.IsPerfect ↥K := hKq.1
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  set ψ : ↥P →* MulAut (Qbar K) := (barHom K).comp (Subgroup.inclusion hPN) with hψ
  have hR2 : IsPGroup 2 ψ.range :=
    IsPGroup.of_surjective hP ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hRne : Nontrivial ψ.range := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h0
    apply hPK
    intro p hp
    have h1 : ψ ⟨p, hp⟩ = 1 := by
      have : ψ ⟨p, hp⟩ ∈ ψ.range := ⟨⟨p, hp⟩, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this
    have h2 := (barHom_eq_one_iff hperf (Subgroup.inclusion hPN ⟨p, hp⟩)).1 h1
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (h2 ⟨k, hk⟩).symm
  have hZnt : Nontrivial (Subgroup.center ↥ψ.range) := hR2.center_nontrivial
  obtain ⟨a, ha⟩ : ∃ a : Subgroup.center ↥ψ.range, orderOf a = 2 := by
    have hZ2 : IsPGroup 2 (Subgroup.center ↥ψ.range) := hR2.to_subgroup _
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hn
    exact exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  obtain ⟨p₀, hp₀⟩ := (a : ↥ψ.range).2
  set t : ↥(Subgroup.normalizer (K : Set Y)) := Subgroup.inclusion hPN p₀ with htdef
  have htP : (t : Y) ∈ P := p₀.2
  have hbt : barHom K t = ((a : ↥ψ.range) : MulAut (Qbar K)) := hp₀
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  refine ⟨t, htP, ?_, ?_, ?_⟩
  · rw [hbt]
    have := congrArg (fun z : Subgroup.center ↥ψ.range => ((z : ↥ψ.range) : MulAut (Qbar K))) ha2
    simpa using this
  · rw [hbt]
    intro h1
    apply ha1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  have hcomm : ∀ x : ↥P, ∀ k ∈ K, ((x : Y)⁻¹ * t * x * (t : Y)⁻¹) * k =
      k * ((x : Y)⁻¹ * t * x * (t : Y)⁻¹) := by
    intro x k hk
    set r : ↥(Subgroup.normalizer (K : Set Y)) := (Subgroup.inclusion hPN x)⁻¹ * t *
      Subgroup.inclusion hPN x * t⁻¹ with hrdef
    have hcen := Subgroup.mem_center_iff.1 a.2 ⟨ψ x, x, rfl⟩
    have hψx : barHom K (Subgroup.inclusion hPN x) * barHom K t =
        barHom K t * barHom K (Subgroup.inclusion hPN x) := by
      rw [hbt]
      have := congrArg (fun z : ↥ψ.range => (z : MulAut (Qbar K))) hcen
      simpa [hψ] using this
    have hr1 : barHom K r = 1 := by
      rw [hrdef, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (barHom K t),
        ← hψx]
      group
    have h := (barHom_eq_one_iff hperf r).1 hr1 ⟨k, hk⟩
    simpa [hrdef] using h
  set X : Subgroup Y := K ⊓ Subgroup.centralizer ({(t : Y)} : Set Y) with hXdef
  have hconj : ∀ x : ↥P, ∀ y ∈ X, (x : Y) * y * (x : Y)⁻¹ ∈ X := by
    intro x y hy
    have hyK : y ∈ K := hy.1
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hPN x.2) y).1 hyK, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    set c : Y := (x : Y)⁻¹ * t * x * (t : Y)⁻¹ with hcdef
    have hxt : (x : Y)⁻¹ * t * x = c * t := by rw [hcdef]; group
    have hcy : c * y = y * c := hcomm x y hyK
    have e1 : (t : Y) = (x : Y) * (c * t) * (x : Y)⁻¹ := by rw [← hxt]; group
    calc (x : Y) * y * (x : Y)⁻¹ * t = (x : Y) * (y * ((x : Y)⁻¹ * t * x)) * (x : Y)⁻¹ := by
          group
      _ = (x : Y) * ((c * y) * t) * (x : Y)⁻¹ := by rw [hxt, hcy]; group
      _ = (x : Y) * (c * (t * y)) * (x : Y)⁻¹ := by rw [mul_assoc c y (t : Y), hyt]
      _ = ((x : Y) * (c * t) * (x : Y)⁻¹) * ((x : Y) * y * (x : Y)⁻¹) := by group
      _ = t * ((x : Y) * y * (x : Y)⁻¹) := by rw [← e1]
  have hPX : P ≤ Subgroup.normalizer (X : Set Y) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj ⟨x, hx⟩ y hy, fun hy => ?_⟩
    have h := hconj ⟨x⁻¹, P.inv_mem hx⟩ _ hy
    simpa [mul_assoc] using h
  set H' : Subgroup Y := X ⊔ P with hH'def
  have hH'H : H' ≤ H := sup_le (inf_le_left.trans hK.1) hPH
  have hH'sq : CFSG.SectionRank.IsSQTKCat ↥H' := CFSG.SectionRank.IsSQTKCat.of_le hH'H hH
  have hPH' : P ≤ H' := le_sup_right
  have hCPt : Subgroup.centralizer (P : Set Y) ≤ Subgroup.centralizer ({(t : Y)} : Set Y) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 htP)
  have hKCPX : K ⊓ Subgroup.centralizer (P : Set Y) ≤ X := inf_le_inf_left _ hCPt
  have hLX : L ≤ X := hL.1.trans hKCPX
  have hH'N : H' ≤ Subgroup.normalizer (K : Set Y) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) hPN
  have hKCP : K ⊓ Subgroup.centralizer (P : Set Y) ≤ H' ⊓ Subgroup.centralizer (P : Set Y) :=
    le_inf (hKCPX.trans le_sup_left) inf_le_right
  have hKCPn : ((K ⊓ Subgroup.centralizer (P : Set Y)).subgroupOf
      (H' ⊓ Subgroup.centralizer (P : Set Y))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKCP]
    intro h hh
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hH'N hh.1, Subgroup.le_normalizer hh.2⟩
  have hLc' : IsComponentIn L (H' ⊓ Subgroup.centralizer (P : Set Y)) :=
    Id2519.isComponentIn_of_mem_cComp (cComp_mem_of_subnormal
      (A3.subnormal_of_normal hKCP hKCPn) (Id2519.mem_cComp_of_isComponentIn hL)) hLq
  have hL2 : Id2519.IsTwoComponentIn L (H' ⊓ Subgroup.centralizer (P : Set Y)) :=
    Id2519.isTwoComponentIn_of_isComponentIn hLc' (two_dvd_card_of_isQuasisimple hLq)
  obtain ⟨⟨φ⟩, hZ⟩ := hL7
  obtain ⟨E, hEL, hE3, hE9⟩ := exists_elemAbelian_nine_of_alt7 φ hZ
  have hm3 : CFSG.Open.pRank 3 L = 2 := by
    refine le_antisymm ?_ ?_
    · have h1 := hH.1 3 Nat.prime_three (by norm_num)
      rw [CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank] at h1
      exact (CFSG.SectionRank.pRank_mono (by norm_num) ((hLX.trans le_sup_left).trans hH'H)).trans
        h1
    · exact CFSG.SectionRank.le_pRank (by norm_num) hEL hE3 (by rw [hE9]; norm_num)
  obtain ⟨K₀, hK₀2, hLK₀, hK₀n, -, hK₀q⟩ := hI31 Y H' P L hH'sq hPH' hP hL2 hm3
  have hK₀H' : K₀ ≤ H' := le_of_mem_cComp hK₀2.1
  have hK₀X : K₀ ≤ X :=
    C2Push.le_of_perfect_le_sup hP hPX (perfect_of_mem_cComp hK₀2.1) hK₀H'
  have hK₀c' : IsComponentIn K₀ H' := Id2519.isComponentIn_of_mem_cComp hK₀2.1 hK₀q
  refine ⟨K₀, hLK₀, BenderBranch.isComponentIn_of_le hK₀c' hK₀X le_sup_left,
    hPH'.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H').1 hK₀n), hK₀c',
    BenderBranch.isComponentIn_of_le hL (le_inf hLK₀ (hL.1.trans inf_le_right))
      (inf_le_inf_right _ (hK₀X.trans inf_le_left))⟩

end Ambient

end E6

end CFSG.Quasithin
