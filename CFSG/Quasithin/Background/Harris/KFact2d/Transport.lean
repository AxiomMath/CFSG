module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Ambient

variable {X : Type} [Group X] {K S : Subgroup X}

theorem mem_zOf_subgroupOf_iff (hSK : S ≤ K) (y : ↥K) :
    y ∈ E2P.zOf (S.subgroupOf K) ↔ (y : X) ∈ E2P.zOf S := by
  unfold E2P.zOf
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun s hs => ?_⟩
    have := h ⟨s, hSK hs⟩ hs
    simpa using congrArg Subtype.val this
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun s hs => ?_⟩
    have := h (s : X) hs
    exact Subtype.ext (by simpa using this)

theorem mem_cenZ_iff (hSK : S ≤ K) (x : X) :
    x ∈ cenZ K S ↔ ∃ y : ↥K, (y : X) = x ∧ y ∈ Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K) := by
  unfold cenZ
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxK, h⟩
    refine ⟨⟨x, hxK⟩, rfl, fun z hz => ?_⟩
    have hz' := (mem_zOf_subgroupOf_iff hSK z).1 hz
    have := h (z : X) hz'
    exact Subtype.ext (by simpa using this)
  · rintro ⟨y, rfl, h⟩
    refine ⟨y.2, fun z hz => ?_⟩
    have hzK : z ∈ K := hSK hz.1
    have := h ⟨z, hzK⟩ ((mem_zOf_subgroupOf_iff hSK ⟨z, hzK⟩).2 hz)
    simpa using congrArg Subtype.val this

end Ambient

section Iso

variable {L L' : Type} [Group L] [Group L']

theorem mem_zOf_map_iff (e : L ≃* L') (U : Subgroup L) (w : L') :
    w ∈ E2P.zOf (U.map e.toMonoidHom) ↔ e.symm w ∈ E2P.zOf U := by
  unfold E2P.zOf
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, h⟩
    refine ⟨by simpa using hu, fun s hs => ?_⟩
    have := h (e s) ⟨s, hs, rfl⟩
    simpa using congrArg e.symm this
  · rintro ⟨hw, h⟩
    refine ⟨⟨e.symm w, hw, by simp⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := h s hs
    apply e.symm.injective
    simpa using this

@[expose] def F2At (L : Type) [Group L] (U : Subgroup L) : Prop :=
  ∃ b ∈ Subgroup.centralizer (E2P.zOf U : Set L) ⊓
      Subgroup.centralizer ((Subgroup.centralizer (E2P.zOf U : Set L) : Subgroup L) : Set L),
    b ≠ 1 ∧ Odd (orderOf b)

theorem F2At.of_map (e : L ≃* L') (U : Subgroup L) (h : F2At L' (U.map e.toMonoidHom)) :
    F2At L U := by
  obtain ⟨b, ⟨hb1, hb2⟩, hb3, hb4⟩ := h
  refine ⟨e.symm b, ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => ?_,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, ?_, ?_⟩
  · have hz' : e z ∈ E2P.zOf (U.map e.toMonoidHom) := (mem_zOf_map_iff e U (e z)).2 (by simpa using hz)
    have := Subgroup.mem_centralizer_iff.mp hb1 (e z) hz'
    apply e.injective
    simpa using this
  · have hy' : e y ∈ Subgroup.centralizer (E2P.zOf (U.map e.toMonoidHom) : Set L') := by
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have hw' := (mem_zOf_map_iff e U w).1 hw
      have := Subgroup.mem_centralizer_iff.mp hy (e.symm w) hw'
      apply e.symm.injective
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hb2 (e y) hy'
    apply e.injective
    simpa using this
  · intro h1
    exact hb3 (by simpa using congrArg e h1)
  · have : orderOf (e.symm b) = orderOf b := MulEquiv.orderOf_eq e.symm b
    rwa [this]

end Iso

variable {X : Type} [Group X] {K S : Subgroup X}

theorem f2_of_model (hSK : S ≤ K) (h : F2At ↥K (S.subgroupOf K)) :
    ∃ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), b ≠ 1 ∧ Odd (orderOf b) := by
  obtain ⟨b, ⟨hb1, hb2⟩, hb3, hb4⟩ := h
  refine ⟨(b : X), ⟨(mem_cenZ_iff hSK _).2 ⟨b, rfl, hb1⟩, ?_⟩, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    obtain ⟨y', rfl, hy'⟩ := (mem_cenZ_iff hSK y).1 hy
    have := Subgroup.mem_centralizer_iff.mp hb2 y' hy'
    simpa using congrArg Subtype.val this
  · intro h1
    exact hb3 (Subtype.ext h1)
  · rw [Subgroup.orderOf_coe]
    exact hb4

@[expose] def F1At (L : Type) [Group L] (U : Subgroup L) : Prop :=
  ∀ E : Subgroup L, IsElemAbelian 2 E → E ≤ U → U ≤ Subgroup.normalizer (E : Set L) →
    E ≤ E2P.zOf U

section
variable {L L' : Type} [Group L] [Group L']

theorem isElemAbelian_map (e : L ≃* L') {E : Subgroup L} (h : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map e.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map h _

theorem F1At.of_map (e : L ≃* L') (U : Subgroup L) (h : F1At L' (U.map e.toMonoidHom)) :
    F1At L U := by
  intro E hE hEU hUN
  have h1 := h (E.map e.toMonoidHom) (isElemAbelian_map e hE) (Subgroup.map_mono hEU) ?_
  · intro x hx
    have := h1 ⟨x, hx, rfl⟩
    simpa using (mem_zOf_map_iff e U (e x)).1 this
  · intro g hg
    obtain ⟨u, hu, rfl⟩ := hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have := Subgroup.mem_normalizer_iff.mp (hUN hu) (e.symm w)
    simp only [Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom]
    simpa [map_mul, map_inv] using this
end

variable {X : Type} [Group X] {K S : Subgroup X}

theorem f1_of_model (hSK : S ≤ K) (h : F1At ↥K (S.subgroupOf K)) :
    ∀ E : Subgroup X, IsElemAbelian 2 E → E ≤ S → S ≤ Subgroup.normalizer (E : Set X) →
      E ≤ E2P.zOf S := by
  intro E hE hES hSN x hx
  have hxK : x ∈ K := hSK (hES hx)
  have hE' : IsElemAbelian 2 (E.subgroupOf K) := by
    obtain ⟨hc, h2⟩ := hE
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      have := hc.is_comm.comm ⟨(a : X), ha⟩ ⟨(b : X), hb⟩
      apply Subtype.ext
      apply Subtype.ext
      have h3 := congrArg (fun z : ↥E => (z : X)) this
      simpa using h3
    · intro y hy
      exact Subtype.ext (by simpa using h2 (y : X) hy)
  have h1 := h (E.subgroupOf K) hE' (fun y hy => by
      simpa [Subgroup.mem_subgroupOf] using hES hy) ?_
  · exact (mem_zOf_subgroupOf_iff hSK ⟨x, hxK⟩).1 (h1 (by simpa [Subgroup.mem_subgroupOf] using hx))
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have := Subgroup.mem_normalizer_iff.mp (hSN (by simpa [Subgroup.mem_subgroupOf] using hs))
      (w : X)
    simpa [Subgroup.mem_subgroupOf] using this

@[expose] def F3At (L : Type) [Group L] (U : Subgroup L) : Prop :=
  ∀ α : MulAut L, α * α = 1 → (∀ y : L, α ≠ MulAut.conj y) → (∀ w ∈ E2P.zOf U, α w = w) →
    ∀ b ∈ Subgroup.centralizer (E2P.zOf U : Set L) ⊓
        Subgroup.centralizer ((Subgroup.centralizer (E2P.zOf U : Set L) : Subgroup L) : Set L),
      Odd (orderOf b) → α b = b⁻¹

section
variable {L L' : Type} [Group L] [Group L']

theorem F3At.of_map (e : L ≃* L') (U : Subgroup L) (h : F3At L' (U.map e.toMonoidHom)) :
    F3At L U := by
  intro α hαα hno hfix b ⟨hb1, hb2⟩ hodd
  set α' : MulAut L' := e.symm.trans (α.trans e) with hα'
  have hα'e : ∀ x, α' (e x) = e (α x) := fun x => by simp [hα']
  have key := h α' (by
      ext x'
      have hx := congrArg (fun f : MulAut L => e (f (e.symm x'))) hαα
      simpa [hα'] using hx)
    (by
      intro y' hy
      apply hno (e.symm y')
      ext x
      have := congrArg (fun f : MulAut L' => e.symm (f (e x))) hy
      simpa [hα'] using this)
    (by
      intro w hw
      have hw' := (mem_zOf_map_iff e U w).1 hw
      have := hfix _ hw'
      have h3 := congrArg e this
      simpa [hα'] using h3)
    (e b) ⟨?_, ?_⟩ (by rwa [MulEquiv.orderOf_eq])
  · have := congrArg e.symm key
    simp [hα'] at this
    exact this
  · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hw' := (mem_zOf_map_iff e U w).1 hw
    have := Subgroup.mem_centralizer_iff.mp hb1 _ hw'
    apply e.symm.injective
    simpa using this
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : e.symm y ∈ Subgroup.centralizer (E2P.zOf U : Set L) := by
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have hw' : e w ∈ E2P.zOf (U.map e.toMonoidHom) := (mem_zOf_map_iff e U (e w)).2 (by simpa using hw)
      have := Subgroup.mem_centralizer_iff.mp hy _ hw'
      apply e.injective
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hb2 _ hy'
    apply e.symm.injective
    simpa using this
end

variable {X : Type} [Group X] {K S : Subgroup X}

theorem f3_of_model (hKn : K.Normal) (hC : Subgroup.centralizer (K : Set X) = ⊥) (hSK : S ≤ K)
    (h : F3At ↥K (S.subgroupOf K)) {u : X} (huu : u * u = 1) (huK : u ∉ K)
    (huz : u ∈ Subgroup.centralizer (E2P.zOf S : Set X)) :
    ∀ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), Odd (orderOf b) →
      u * b * u⁻¹ = b⁻¹ := by
  intro b ⟨hb1, hb2⟩ hodd
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  obtain ⟨b', rfl, hb'1⟩ := (mem_cenZ_iff hSK b).1 hb1
  set α : MulAut ↥K := MulAut.conjNormal u with hα
  have hαc : ∀ k : ↥K, ((α k : ↥K) : X) = u * k * u⁻¹ := fun k => rfl
  have key := h α (by
      ext k
      rw [MulAut.mul_apply, hαc, hαc, MulAut.one_apply]
      rw [hui]
      calc u * (u * (k : X) * u) * u = (u * u) * k * (u * u) := by simp [mul_assoc]
        _ = k := by rw [huu]; simp)
    (by
      intro y hy
      apply huK
      have hall : ∀ k : ↥K, (y : X)⁻¹ * u * k = k * ((y : X)⁻¹ * u) := by
        intro k
        have := congrArg (fun f : MulAut ↥K => ((f k : ↥K) : X)) hy
        simp only [hαc, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
        have h2 : (u : X) * k = (y : X) * k * (y : X)⁻¹ * u := by
          calc (u : X) * k = (u * k * u⁻¹) * u := by group
            _ = _ := by rw [this]
        calc (y : X)⁻¹ * u * k = (y : X)⁻¹ * (u * k) := by group
          _ = (y : X)⁻¹ * ((y : X) * k * (y : X)⁻¹ * u) := by rw [h2]
          _ = k * ((y : X)⁻¹ * u) := by group
      have hmem : (y : X)⁻¹ * u ∈ Subgroup.centralizer (K : Set X) :=
        Subgroup.mem_centralizer_iff.mpr fun k hk => (hall ⟨k, hk⟩).symm
      rw [hC, Subgroup.mem_bot] at hmem
      have : u = y := by
        calc u = y * ((y : X)⁻¹ * u) := by group
          _ = y := by rw [hmem]; simp
      rw [this]
      exact y.2)
    (by
      intro w hw
      apply Subtype.ext
      rw [hαc]
      have hw' := (mem_zOf_subgroupOf_iff hSK w).1 hw
      have := Subgroup.mem_centralizer_iff.mp huz _ hw'
      calc u * (w : X) * u⁻¹ = (w : X) * u * u⁻¹ := by rw [← this]
        _ = w := by simp)
    b' ⟨hb'1, ?_⟩ (by rwa [Subgroup.orderOf_coe] at hodd)
  · have := congrArg Subtype.val key
    rw [hαc] at this
    simpa using this
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hyc : (y : X) ∈ cenZ K S := (mem_cenZ_iff hSK _).2 ⟨y, rfl, hy⟩
    have := Subgroup.mem_centralizer_iff.mp hb2 _ hyc
    exact Subtype.ext (by simpa using this)

end CFSG.Quasithin.Background.Harris.KFact2d
