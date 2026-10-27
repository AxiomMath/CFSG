module

public import CFSG.Quasithin.EmptyFaithful.R3c9Bnd
public import CFSG.Quasithin.EmptyFaithful.R3c8Lie

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G3a CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LieType.BorelTits
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement

section KLemma

variable {X : Type} [Group X]

@[expose] def twistSub (N : Subgroup X) (α : MulAut X) : Subgroup X :=
  Subgroup.closure (Set.range fun b : N => (b : X)⁻¹ * α b)

theorem mem_twistSub (N : Subgroup X) (α : MulAut X) {b : X} (hb : b ∈ N) :
    b⁻¹ * α b ∈ twistSub N α :=
  Subgroup.subset_closure ⟨⟨b, hb⟩, rfl⟩

theorem twistSub_le {N : Subgroup X} {α : MulAut X} (hα : ∀ b ∈ N, α b ∈ N) :
    twistSub N α ≤ N := by
  rw [twistSub, Subgroup.closure_le]
  rintro _ ⟨⟨b, hb⟩, rfl⟩
  exact N.mul_mem (N.inv_mem hb) (hα b hb)

theorem twistSub_centralizes {N : Subgroup X} {α : MulAut X} {A : Subgroup X}
    (hNA : N ≤ Subgroup.normalizer (A : Set X)) (hA : ∀ a ∈ A, α a = a) :
    twistSub N α ≤ Subgroup.centralizer (A : Set X) := by
  rw [twistSub, Subgroup.closure_le]
  rintro _ ⟨⟨b, hb⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hNA hb) a).mp ha
  have h2 : α (b * a * b⁻¹) = b * a * b⁻¹ := hA _ h1
  have h3 : α (b * a * b⁻¹) = α b * a * (α b)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hA a ha]
  have h4 : α b * a * (α b)⁻¹ = b * a * b⁻¹ := h3.symm.trans h2
  have h5 : (b⁻¹ * α b) * a * (b⁻¹ * α b)⁻¹ = a := by
    calc (b⁻¹ * α b) * a * (b⁻¹ * α b)⁻¹ = b⁻¹ * (α b * a * (α b)⁻¹) * b := by group
      _ = b⁻¹ * (b * a * b⁻¹) * b := by rw [h4]
      _ = a := by group
  calc a * (b⁻¹ * α b) = ((b⁻¹ * α b) * a * (b⁻¹ * α b)⁻¹) * (b⁻¹ * α b) := by rw [h5]
    _ = (b⁻¹ * α b) * a := by group

theorem twistSub_conj {N : Subgroup X} {α : MulAut X} {c : X} (hc : c ∈ N)
    {k : X} (hk : k ∈ twistSub N α) : c⁻¹ * k * c ∈ twistSub N α := by
  have key : twistSub N α ≤ (twistSub N α).comap (MulAut.conj c⁻¹).toMonoidHom := by
    rw [twistSub, Subgroup.closure_le]
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have e : (MulAut.conj c⁻¹).toMonoidHom (b⁻¹ * α b) =
        ((b * c)⁻¹ * α (b * c)) * (c⁻¹ * α c)⁻¹ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv,
        map_mul]
      group
    rw [e]
    exact (twistSub N α).mul_mem (mem_twistSub N α (N.mul_mem hb hc))
      ((twistSub N α).inv_mem (mem_twistSub N α hc))
  have := key hk
  rw [Subgroup.mem_comap] at this
  simpa [MulAut.conj_apply] using this

theorem eq_of_twistSub_eq_bot {N : Subgroup X} {α : MulAut X} (h : twistSub N α = ⊥) :
    ∀ b ∈ N, α b = b := by
  intro b hb
  have := mem_twistSub N α hb
  rw [h, Subgroup.mem_bot] at this
  have h1 : b⁻¹ * α b = 1 := this
  calc α b = b * (b⁻¹ * α b) := by group
    _ = b := by rw [h1, mul_one]

end KLemma

section Borel

variable {X : Type} [Group X] [Finite X]

theorem twist_eq_bot_of_borel {T Zc : Subgroup X}
    (hcent : ∀ x : X, (∀ t ∈ T, x * t = t * x) → x ∈ T) (hZ1 : Zc ≠ ⊥)
    (hcen : ∀ E : Subgroup X, E ≤ T → E ≠ ⊥ →
      Subgroup.normalizer (T : Set X) ≤ Subgroup.normalizer (E : Set X) → Zc ≤ E)
    {α : MulAut X} (hαT : ∀ t : X, t ∈ T ↔ α t ∈ T) {A V : Subgroup X}
    (hNA : Subgroup.normalizer (T : Set X) ≤ Subgroup.normalizer (A : Set X))
    (hA : ∀ a ∈ A, α a = a) (hVT : V ≤ T) (hV1 : V ≠ ⊥)
    (hNV : Subgroup.normalizer (T : Set X) ≤ Subgroup.normalizer (V : Set X))
    (hVA : ∀ x ∈ V, (∀ a ∈ A, a * x = x * a) → x = 1) :
    ∀ b ∈ Subgroup.normalizer (T : Set X), α b = b := by
  classical
  set N : Subgroup X := Subgroup.normalizer (T : Set X) with hN
  have hαN : ∀ b ∈ N, α b ∈ N := by
    intro b hb
    rw [hN, Subgroup.mem_normalizer_iff]
    intro t
    obtain ⟨t', rfl⟩ : ∃ t', t = α t' := ⟨α.symm t, (α.apply_symm_apply t).symm⟩
    have h1 := Subgroup.mem_normalizer_iff.mp hb t'
    have e2 : α b * α t' * (α b)⁻¹ = α (b * t' * b⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [e2, ← hαT t', ← hαT (b * t' * b⁻¹)]
    exact h1
  apply eq_of_twistSub_eq_bot
  set K : Subgroup X := twistSub N α with hK
  by_contra hKne
  have hKN : K ≤ N := twistSub_le hαN
  have hKA : K ≤ Subgroup.centralizer (A : Set X) := twistSub_centralizes hNA hA
  have hconj : ∀ c ∈ N, ∀ k ∈ K, c⁻¹ * k * c ∈ K := fun c hc k hk => twistSub_conj hc hk
  have hconj' : ∀ c ∈ N, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have := hconj c⁻¹ (N.inv_mem hc) k hk
    simpa using this
  have hE1 : K ⊓ T ≠ ⊥ := by
    intro hEb
    apply hKne
    rw [eq_bot_iff]
    intro k hk
    have hkN : k ∈ N := hKN hk
    have hkc : ∀ t ∈ T, k * t = t * k := by
      intro t ht
      have h1 : k * t * k⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hkN t).mp ht
      have h2 : t * k⁻¹ * t⁻¹ ∈ K := hconj' t (Subgroup.le_normalizer ht) k⁻¹ (K.inv_mem hk)
      have h3 : k * t * k⁻¹ * t⁻¹ ∈ K ⊓ T :=
        ⟨by
          have := K.mul_mem hk h2
          have e : k * (t * k⁻¹ * t⁻¹) = k * t * k⁻¹ * t⁻¹ := by group
          rwa [e] at this,
         T.mul_mem h1 (T.inv_mem ht)⟩
      rw [hEb, Subgroup.mem_bot] at h3
      calc k * t = (k * t * k⁻¹ * t⁻¹) * (t * k) := by group
        _ = t * k := by rw [h3, one_mul]
    have hkT : k ∈ T := hcent k hkc
    have : k ∈ K ⊓ T := ⟨hk, hkT⟩
    rwa [hEb] at this
  have hEN : N ≤ Subgroup.normalizer ((K ⊓ T : Subgroup X) : Set X) := by
    intro n hn
    refine A4.mem_normalizer_of_conj_mem fun e he => ⟨hconj' n hn e he.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp hn e).mp he.2
  have hZE : Zc ≤ K ⊓ T := hcen _ inf_le_right hE1 hEN
  have hZV : Zc ≤ V := hcen V hVT hV1 hNV
  apply hZ1
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  refine hVA z (hZV hz) fun a ha => ?_
  exact Subgroup.mem_centralizer_iff.mp (hKA (hZE hz).1) a ha

structure BorelData (Y : Type) [Group Y] [Finite Y] : Prop where
  pkg : R3c8.BorelPkg Y
  center : ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ → ∃ Zc : Subgroup Y, Zc ≠ ⊥ ∧
    ∀ E : Subgroup Y, E ≤ T → E ≠ ⊥ →
      Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (E : Set Y) → Zc ≤ E

theorem borelData_of_bender {Y : Type} [Group Y] [Finite Y]
    (hB : fusionIsBenderGroup Y) (hpkg : R3c8.BorelPkg Y) : BorelData Y := by
  refine ⟨hpkg, fun T hT => ?_⟩
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  obtain ⟨D, hD⟩ := exists_borelSetup hB T'
  refine ⟨sylowCenter (T' : Subgroup Y), ?_,
    fun E hET hE1 hN => R3c9.bender_center_le hB T' hET hE1 hN⟩
  intro hbot
  have h4 := hD.four
  rw [hbot, Subgroup.card_bot] at h4
  omega

end Borel

section Glue

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_le_of_isSylowTwoOf {L Q : Subgroup G} (hZ : centerOf L = pCoreOf 2 L)
    (hQ : IsSylowTwoOf Q L) : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Q := by
  intro z hz
  have h1 : (z : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hz
  rw [hZ] at h1
  exact QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQ h1

theorem exists_quotSylow {L Q : Subgroup G} (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L) :
    ∃ Tsyl : Sylow 2 (↥L ⧸ Subgroup.center ↥L),
      (Tsyl : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
          (Q.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∧
      (Tsyl : Subgroup (↥L ⧸ Subgroup.center ↥L)).comap (QuotientGroup.mk' (Subgroup.center ↥L)) =
          Q.subgroupOf L ∧
      (Subgroup.normalizer ((Tsyl : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
          Set (↥L ⧸ Subgroup.center ↥L))).comap (QuotientGroup.mk' (Subgroup.center ↥L)) =
        Subgroup.normalizer ((Q.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  have hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Q := center_le_of_isSylowTwoOf hZ hQ
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker = Subgroup.center ↥L :=
    QuotientGroup.ker_mk' _
  have hZP' : Subgroup.center ↥L ≤ Q.subgroupOf L := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hZP z hz)
  let Tsyl : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := (A4.toSylow hQ).mapSurjective hsurj
  have hT : (Tsyl : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
      (Q.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [Sylow.coe_mapSurjective, A4.toSylow_coe]
  have hTcomap : (Tsyl : Subgroup (↥L ⧸ Subgroup.center ↥L)).comap
      (QuotientGroup.mk' (Subgroup.center ↥L)) = Q.subgroupOf L := by
    rw [hT]
    exact Subgroup.comap_map_eq_self (by rw [hker]; exact hZP')
  refine ⟨Tsyl, hT, hTcomap, ?_⟩
  rw [Subgroup.comap_normalizer_eq_of_surjective _ hsurj, hTcomap]

theorem centralizes_of_borel_fixed {L Q A V : Subgroup G} {v : G}
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hD : BorelData (↥L ⧸ Subgroup.center ↥L))
    (hvL : v ∈ Subgroup.normalizer (L : Set G)) (hvQ : v ∈ Subgroup.normalizer (Q : Set G))
    (hv2 : v * v = 1)
    (hAL : A ≤ L) (hBA : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hvA : ∀ a ∈ A, v * a = a * v)
    (hVQ : V ≤ Q) (hBV : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVnZ : ¬ V ≤ centerOf L)
    (hVA : ∀ x ∈ V, (∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ centerOf L) → x ∈ centerOf L) :
    v ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : Q ≤ L := hQ.1
  have hchar : (Subgroup.center ↥L).Characteristic := inferInstance
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set P' : Subgroup ↥L := Q.subgroupOf L with hP'
  set T : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  have hTsyl : IsSylowTwoOf T ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  set α : MulAut (↥L ⧸ Z) := SteinbergBS.conjQuotientHom L Z ⟨v, hvL⟩ with hα
  have hαl : ∀ l : ↥L, α (π l) = π (Subgroup.normalizerMonoidHom L ⟨v, hvL⟩ l) := fun l => rfl
  have hαcoe : ∀ l : ↥L,
      ((Subgroup.normalizerMonoidHom L ⟨v, hvL⟩ l : ↥L) : G) = v * l * v⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨v, hvL⟩ l
  have hαinv : ∀ y, α (α y) = y := by
    intro y
    obtain ⟨l, rfl⟩ := hsurj y
    rw [hαl, hαl]
    congr 1
    apply Subtype.ext
    rw [hαcoe, hαcoe]
    calc v * (v * (l : G) * v⁻¹) * v⁻¹ = (v * v) * (l : G) * (v * v)⁻¹ := by group
      _ = l := by rw [hv2]; group
  have hαT : ∀ t : ↥L ⧸ Z, t ∈ T ↔ α t ∈ T := by
    intro t
    obtain ⟨l, rfl⟩ := hsurj t
    rw [hαl]
    have h1 : π l ∈ T ↔ l ∈ P' := by rw [← Subgroup.mem_comap, hTcomap]
    have h2 : π (Subgroup.normalizerMonoidHom L ⟨v, hvL⟩ l) ∈ T ↔
        (Subgroup.normalizerMonoidHom L ⟨v, hvL⟩ l) ∈ P' := by
      rw [← Subgroup.mem_comap, hTcomap]
    rw [h1, h2, hP', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hαcoe]
    exact Subgroup.mem_normalizer_iff.mp hvQ l
  set Abar : Subgroup (↥L ⧸ Z) := (A.subgroupOf L).map π with hAbar
  set Vbar : Subgroup (↥L ⧸ Z) := (V.subgroupOf L).map π with hVbar
  have hVL : V ≤ L := hVQ.trans hPL
  have hNT : ∀ x ∈ Subgroup.normalizer (T : Set (↥L ⧸ Z)),
      ∃ l : ↥L, π l = x ∧ (l : G) ∈ L ⊓ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨l, rfl⟩ := hsurj x
    have hl : l ∈ Subgroup.normalizer (P' : Set ↥L) := by rw [← hNcomap]; exact hx
    have hlN : (l : G) ∈ Subgroup.normalizer (Q : Set G) :=
      (SBc2.mem_normalizer_subgroupOf_iff hPL l).mp hl
    exact ⟨l, rfl, l.2, hlN⟩
  have hNA : Subgroup.normalizer (T : Set (↥L ⧸ Z)) ≤
      Subgroup.normalizer (Abar : Set (↥L ⧸ Z)) := by
    intro x hx
    obtain ⟨l, rfl, hlB⟩ := hNT x hx
    have hlA : (l : G) ∈ Subgroup.normalizer (A : Set G) := hBA hlB
    have hlA' : l ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hAL l).mpr hlA
    refine A4.mem_normalizer_of_conj_mem fun abar habar => ?_
    obtain ⟨a, ha, rfl⟩ := habar
    refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlA' a).mp ha, ?_⟩
    simp [map_mul, map_inv]
  have hNV : Subgroup.normalizer (T : Set (↥L ⧸ Z)) ≤
      Subgroup.normalizer (Vbar : Set (↥L ⧸ Z)) := by
    intro x hx
    obtain ⟨l, rfl, hlB⟩ := hNT x hx
    have hlV : (l : G) ∈ Subgroup.normalizer (V : Set G) := hBV hlB
    have hlV' : l ∈ Subgroup.normalizer ((V.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hVL l).mpr hlV
    refine A4.mem_normalizer_of_conj_mem fun vbar hvbar => ?_
    obtain ⟨a, ha, rfl⟩ := hvbar
    refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlV' a).mp ha, ?_⟩
    simp [map_mul, map_inv]
  have hA : ∀ a ∈ Abar, α a = a := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hαl]
    congr 1
    apply Subtype.ext
    rw [hαcoe]
    have h1 := hvA (a : G) (Subgroup.mem_subgroupOf.mp ha)
    calc v * (a : G) * v⁻¹ = (a : G) * v * v⁻¹ := by rw [h1]
      _ = a := by group
  have hVT : Vbar ≤ T := by
    rw [hT]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.mpr (hVQ (Subgroup.mem_subgroupOf.mp hx))
  have hV1 : Vbar ≠ ⊥ := by
    intro hb
    apply hVnZ
    intro x hx
    have hxL : x ∈ L := hVL hx
    have hmem : π ⟨x, hxL⟩ ∈ Vbar := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    have : (⟨x, hxL⟩ : ↥L) ∈ π.ker := hmem
    rw [hker] at this
    exact SBc2.mem_centerOf_iff_center.mpr this
  have hVA' : ∀ x ∈ Vbar, (∀ a ∈ Abar, a * x = x * a) → x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩ hc
    have hxV : (x₀ : G) ∈ V := Subgroup.mem_subgroupOf.mp hx₀
    have hcen : (x₀ : G) ∈ centerOf L := by
      refine hVA _ hxV fun a ha => ?_
      have haL : a ∈ L := hAL ha
      have h1 := hc (π ⟨a, haL⟩) ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have h3 : π (x₀ * ⟨a, haL⟩ * x₀⁻¹ * ⟨a, haL⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      have hmem : (x₀ * ⟨a, haL⟩ * x₀⁻¹ * ⟨a, haL⟩⁻¹ : ↥L) ∈ Z := by
        rw [← hker]
        exact h3
      exact SBc2.mem_centerOf_iff_center.mpr hmem
    have : x₀ ∈ Z := SBc2.mem_centerOf_iff_center.mp hcen
    rw [← hker] at this
    exact this
  obtain ⟨Zc, hZc1, hZc⟩ := hD.center T hTsyl
  have hcentT : ∀ x : ↥L ⧸ Z, (∀ t ∈ T, x * t = t * x) → x ∈ T := hD.pkg.cent T hTsyl
  have hFix := twist_eq_bot_of_borel hcentT hZc1 hZc hαT hNA hA hVT hV1 hNV hVA'
  have hα1 : α = 1 := hD.pkg.rigid T hTsyl α hαinv hFix
  have hvCq : v ∈ SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z := by
    rw [SteinbergBS.mem_quotientCentralizer_iff]
    refine ⟨Subgroup.mem_top _, hvL, fun l hl => ?_⟩
    have h := congrArg (fun f : MulAut (↥L ⧸ Z) => f (π ⟨l, hl⟩)) hα1
    simp only [MulAut.one_apply] at h
    rw [hαl, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at h
    refine ⟨_, h, ?_⟩
    simp [hαcoe, div_eq_mul_inv]
  have hle : ⁅L, SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z⁆ ≤
      Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    rw [SteinbergBS.mem_quotientCentralizer_iff] at hx
    obtain ⟨-, -, hx3⟩ := hx
    have hxl := hx3 l hl
    have hmem : ⁅l, x⁆ ∈ Z.map L.subtype := by
      have := (Z.map L.subtype).inv_mem hxl
      have e : ⁅l, x⁆ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact this
    obtain ⟨z, hz, hzeq⟩ := hmem
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
    rw [← hzeq]
    exact congrArg Subtype.val this
  have hbot := S153D.commutator_eq_bot_of_quasisimple hq hle
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hm : ⁅l, v⁆ ∈ ⁅L, SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z⁆ :=
    Subgroup.commutator_mem_commutator hl hvCq
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
  exact hm

theorem le_normalizer_or_le_of_bender {L Q H : Subgroup G}
    (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hB : fusionIsBenderGroup (↥L ⧸ Subgroup.center ↥L)) (hQH : Q ≤ H) (hHL : H ≤ L) :
    H ≤ Subgroup.normalizer (Q : Set G) ∨ L ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : Q ≤ L := hQ.1
  have hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Q := center_le_of_isSylowTwoOf hZ hQ
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set P' : Subgroup ↥L := Q.subgroupOf L with hP'
  have hXs : IsSimpleGroup (↥L ⧸ Z) := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨D, hD⟩ := exists_borelSetup hB Tsyl
  set Hbar : Subgroup (↥L ⧸ Z) := (H.subgroupOf L).map π with hHbar
  have hTH : (Tsyl : Subgroup (↥L ⧸ Z)) ≤ Hbar := by
    rw [hT]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.mpr (hQH (Subgroup.mem_subgroupOf.mp hx))
  by_cases hH : Hbar = ⊤
  · right
    intro l hl
    have hmem : π ⟨l, hl⟩ ∈ Hbar := by rw [hH]; exact Subgroup.mem_top _
    obtain ⟨h, hh, hhl⟩ := hmem
    have h1 : h⁻¹ * ⟨l, hl⟩ ∈ Z := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hhl]
      group
    have h2 : ((h⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ Q := hZP _ h1
    have h3 : (h : G) ∈ H := Subgroup.mem_subgroupOf.mp hh
    have h4 : (l : G) = (h : G) * ((h⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [h4]
    exact H.mul_mem h3 (hQH h2)
  · left
    have hle := hD.le_normalizer_of_le hTH hH
    intro g hg
    have hgL : g ∈ L := hHL hg
    have hmem : π ⟨g, hgL⟩ ∈ Subgroup.normalizer ((Tsyl : Subgroup (↥L ⧸ Z)) : Set (↥L ⧸ Z)) :=
      hle ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have h1 : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.normalizer (P' : Set ↥L) := by
      rw [← hNcomap]
      exact hmem
    exact (SBc2.mem_normalizer_subgroupOf_iff hPL ⟨g, hgL⟩).mp h1

end Glue

section PSL2

theorem borelPkg_psl2 {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (h : IsPSL 2 2 f X) : R3c8.BorelPkg X := by
  have hB : fusionIsBenderGroup X := A5.C25.fusionIsBenderGroup_of_isPSL h
  have hs : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hb : E2.IsBenderOf f X := ⟨hf, Or.inl h⟩
  exact ⟨borelRigid_of_isBenderOf hb, R3c8.sylowCent_of_isBenderOf hs hb⟩

end PSL2

end CFSG.Quasithin.R3c10
