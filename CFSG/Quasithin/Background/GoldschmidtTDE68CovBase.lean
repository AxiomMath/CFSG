module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Bar
public import CFSG.Quasithin.Background.E6EightSmall
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.Quasithin.E6.Inn

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.Bar

section Lambda

variable {Λ : Type*} [Group Λ]

theorem conj_mem_centralizer_of_mk_mem {y g : Λ}
    (hg : (QuotientGroup.mk g : Λ ⧸ center Λ) ∈
      centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)))
    {d : Λ} (hd : d ∈ centralizer ({y} : Set Λ)) : g * d * g⁻¹ ∈ centralizer ({y} : Set Λ) := by
  have h1 : (QuotientGroup.mk g : Λ ⧸ center Λ) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk g := mem_centralizer_singleton_iff.mp hg
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  set c : Λ := (g * y)⁻¹ * (y * g) with hcdef
  have hc : c ∈ center Λ := h1
  have hy : g⁻¹ * y * g = y * c := by rw [hcdef]; group
  have hdy : d * y = y * d := mem_centralizer_singleton_iff.mp hd
  have hdc : d * c = c * d := Subgroup.mem_center_iff.mp hc d
  rw [mem_centralizer_singleton_iff]
  have e1 : d * (g⁻¹ * y * g) = (g⁻¹ * y * g) * d := by
    rw [hy]
    calc d * (y * c) = (d * y) * c := by group
      _ = (y * d) * c := by rw [hdy]
      _ = y * (d * c) := by group
      _ = y * (c * d) := by rw [hdc]
      _ = (y * c) * d := by group
  calc (g * d * g⁻¹) * y = g * (d * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * d) * g⁻¹ := by rw [e1]
    _ = y * (g * d * g⁻¹) := by group

theorem map_centralizer_le (y : Λ) :
    (centralizer ({y} : Set Λ)).map (QuotientGroup.mk' (center Λ)) ≤
      centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_singleton_iff.mp hd
  show (QuotientGroup.mk d : Λ ⧸ center Λ) * QuotientGroup.mk y =
    QuotientGroup.mk y * QuotientGroup.mk d
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem map_centralizer_normal (y : Λ) :
    (((centralizer ({y} : Set Λ)).map (QuotientGroup.mk' (center Λ))).subgroupOf
      (centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)))).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (map_centralizer_le y)]
  have key : ∀ g ∈ centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)),
      ∀ x ∈ (centralizer ({y} : Set Λ)).map (QuotientGroup.mk' (center Λ)),
        g * x * g⁻¹ ∈ (centralizer ({y} : Set Λ)).map (QuotientGroup.mk' (center Λ)) := by
    intro g hg x hx
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨g₀ * d * g₀⁻¹, conj_mem_centralizer_of_mk_mem hg hd, ?_⟩
    simp [QuotientGroup.mk'_apply]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using h

theorem false_of_component_of_centralizer
    (hfree : ∀ t : Λ ⧸ center Λ, orderOf t = 2 →
      ∀ B : Subgroup (centralizer ({t} : Set (Λ ⧸ center Λ))), ¬ CFSG.IsComponent B)
    {y : Λ} (hy : orderOf (QuotientGroup.mk y : Λ ⧸ center Λ) = 2)
    {K : Subgroup Λ} (hK : K ≤ centralizer ({y} : Set Λ)) (hq : CFSG.IsQuasisimple ↥K)
    (hsub : (K.subgroupOf (centralizer ({y} : Set Λ))).IsSubnormal) : False := by
  classical
  set π : Λ →* Λ ⧸ center Λ := QuotientGroup.mk' (center Λ) with hπ
  set D : Subgroup Λ := centralizer ({y} : Set Λ) with hD
  set C : Subgroup (Λ ⧸ center Λ) :=
    centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)) with hC
  have hDC : D.map π ≤ C := map_centralizer_le y
  have hKD' : K.map π ≤ D.map π := Subgroup.map_mono hK
  have hKC : K.map π ≤ C := hKD'.trans hDC
  have hsub1 : ((K.map π).subgroupOf (D.map π)).IsSubnormal := by
    have h := Subgroup.IsSubnormal.map (MonoidHom.subgroupMap_surjective π D) hsub
    have heq : (K.subgroupOf D).map (π.subgroupMap D) = (K.map π).subgroupOf (D.map π) := by
      ext z
      constructor
      · rintro ⟨⟨d, hdD⟩, hdK, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr ⟨d, Subgroup.mem_subgroupOf.mp hdK, rfl⟩
      · intro hz
        obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
        exact ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
    rwa [heq] at h
  have hsub2 : ((K.map π).subgroupOf C).IsSubnormal := by
    have hnorm : ((D.map π).subgroupOf C).Normal := map_centralizer_normal y
    have hle : (K.map π).subgroupOf C ≤ (D.map π).subgroupOf C := fun x hx => hKD' hx
    have hsn : (((K.map π).subgroupOf C).subgroupOf ((D.map π).subgroupOf C)).IsSubnormal := by
      have h := hsub1.comap (subgroupOfEquivOfLe hDC).toMonoidHom
      convert h using 1
      ext x
      rfl
    exact Subgroup.IsSubnormal.trans hle hsn (Subgroup.Normal.isSubnormal hnorm)
  obtain ⟨k0, hk0K, hk0⟩ : ∃ k ∈ K, π k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have ha : (a₀ : Λ) ∈ center Λ := (QuotientGroup.eq_one_iff (a₀ : Λ)).1 (hcon a₀ a₀.2)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp ha b₀).symm
  have hqB : CFSG.IsQuasisimple ↥((K.map π).subgroupOf C) := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
      (φ := ((subgroupOfEquivOfLe hKC).symm.toMonoidHom).comp (π.subgroupMap K)) hq ?_ ?_
    · exact (subgroupOfEquivOfLe hKC).symm.surjective.comp (MonoidHom.subgroupMap_surjective π K)
    · refine ⟨⟨k0, hk0K⟩, fun h1 => hk0 ?_⟩
      have h2 := congrArg (fun z : ↥((K.map π).subgroupOf C) => ((z : C) : Λ ⧸ center Λ)) h1
      exact h2
  exact hfree _ hy _ ⟨hqB, hsub2⟩

theorem center_eq_bot_of_isQuasisimple_of_simple {X : Type*} [Group X]
    (hq : CFSG.IsQuasisimple X) (hs : IsSimpleGroup X) : center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a₀) b₀).symm

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem not_isComponent_of_isSolvable {C : Type*} [Group C] [Group.IsSolvable C]
    (B : Subgroup C) : ¬ CFSG.IsComponent B := by
  rintro ⟨hq, -⟩
  obtain ⟨hperf, -, a, b, hab⟩ := hq
  have hB : Group.IsSolvable ↥B := Group.isSolvable_of_isSolvable_injective B.subtype_injective
  have hnt : Nontrivial ↥B := by
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subsingleton.elim (a₀ * b₀) (b₀ * a₀)])
  have : Group.IsPerfect ↥B := hperf
  exact Group.IsPerfect.not_isSolvable ↥B hB

@[expose] def InvolFixInner (X : Type*) [Group X] : Prop :=
  ∀ Q : Subgroup X, IsSylowTwoOf Q ⊤ → ∀ β : X ≃* X, (∀ w, β (β w) = w) →
    (∀ q ∈ Q, β q = q) → ∃ x : X, ∀ w, β w = x⁻¹ * w * x

theorem InvolFixInner.of_forall {X : Type*} [Group X]
    (h : ∀ Q : Subgroup X, IsSylowTwoOf Q ⊤ → ∀ β : X ≃* X, (∀ q ∈ Q, β q = q) →
      ∃ x : X, ∀ w, β w = x⁻¹ * w * x) : InvolFixInner X :=
  fun Q hQ β _ hβ => h Q hQ β hβ

theorem InvolFixInner.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : InvolFixInner Y) : InvolFixInner X := by
  intro Q hQ β hβ2 hβ
  have hQ' : IsSylowTwoOf (Q.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hQ.2.1.map e.toMonoidHom, ?_⟩
    have h1 : ((Q.map e.toMonoidHom).subgroupOf ⊤).index = (Q.map e.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have h2 : (Q.subgroupOf ⊤).index = Q.index := Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective Q]
    have := hQ.2.2
    rwa [h2] at this
  obtain ⟨x, hx⟩ := h _ hQ' (e.symm.trans (β.trans e))
    (fun w => by simp [hβ2]) (by
      rintro _ ⟨q, hq, rfl⟩
      simp [hβ q hq])
  refine ⟨e.symm x, fun w => ?_⟩
  have h1 := hx (e w)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  have h2 : β w = e.symm (x⁻¹ * e w * x) := by rw [← h1]; simp
  rw [h2, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end Lambda

section Ambient

variable {Y : Type} [Group Y] {L R : Subgroup Y} {u : Y}

theorem isSylowTwoOf_map_mk (h : E68CentHyp L R u) :
    IsSylowTwoOf (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L))) ⊤ := by
  have hS := h.sylow
  refine ⟨le_top, ?_, ?_⟩
  · exact (hS.2.1.of_equiv (subgroupOfEquivOfLe hS.1).symm).map _
  · intro hdvd
    apply hS.2.2
    refine hdvd.trans ?_
    have h1 : (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L))).relIndex ⊤ =
        (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L))).index :=
      Subgroup.relIndex_top_right _
    have h2 : ((((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L))).subgroupOf ⊤).index =
        (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L))).relIndex ⊤ := rfl
    rw [h2, h1]
    exact Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)

theorem exists_inner_lift (h : E68CentHyp L R u) (hfix : InvolFixInner (Qbar L)) :
    ∃ y : ↥L, orderOf (QuotientGroup.mk y : Qbar L) = 2 ∧
      ∀ x : ↥L, u * (x : Y) * u⁻¹ = (y : Y) * x * (y : Y)⁻¹ := by
  classical
  have hperf : Group.IsPerfect ↥L := h.quasisimple.1
  have hcenter : center (Qbar L) = ⊥ := by
    obtain ⟨-, hs, a, b, hab⟩ := h.quasisimple
    rcases hs.eq_bot_or_eq_top_of_normal (center (Qbar L)) with h1 | h1
    · exact h1
    · exact absurd (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a) hab
  set u' : ↥(normalizer (L : Set Y)) := ⟨u, h.normalizer h.mem⟩ with hu'
  have hfixed : ∀ q ∈ ((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L)),
      barHom L u' q = q := by
    rintro _ ⟨p, hp, rfl⟩
    exact barHom_mk_of_comm u' p (h.central p (Subgroup.mem_inf.mp hp).1)
  have hu2 : u' * u' = 1 := Subtype.ext (by simpa [pow_two] using h.sq)
  have hinvol : ∀ w, barHom L u' (barHom L u' w) = w := by
    intro w
    have h1 : barHom L u' * barHom L u' = 1 := by rw [← map_mul, hu2, map_one]
    simpa using congrArg (fun φ : MulAut (Qbar L) => φ w) h1
  obtain ⟨x, hx⟩ := hfix _ (isSylowTwoOf_map_mk h) (barHom L u') hinvol hfixed
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective x⁻¹
  have hb : barHom L u' = MulAut.conj (QuotientGroup.mk y₀ : Qbar L) := by
    refine MulEquiv.ext fun w => ?_
    rw [hx w, MulAut.conj_apply, hy₀, inv_inv]
  set g : ↥(normalizer (L : Set Y)) := ⟨(y₀ : Y), Subgroup.le_normalizer y₀.2⟩ with hg
  have hbg : barHom L g = MulAut.conj (QuotientGroup.mk y₀ : Qbar L) := barHom_of_mem y₀
  have hone : barHom L (g⁻¹ * u') = 1 := by
    rw [map_mul, map_inv, hbg, hb, inv_mul_cancel]
  have hcomm := (barHom_eq_one_iff hperf (g⁻¹ * u')).1 hone
  have hsq : barHom L (u' * u') = 1 := by rw [hu2, map_one]
  refine ⟨y₀, ?_, ?_⟩
  · rw [map_mul, hb, ← map_mul] at hsq
    have hz : (QuotientGroup.mk y₀ * QuotientGroup.mk y₀ : Qbar L) ∈ center (Qbar L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have := congrArg (fun φ : MulAut (Qbar L) => φ w) hsq
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hcenter, Subgroup.mem_bot] at hz
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two]; exact hz) fun h1 => ?_
    rw [h1, map_one] at hb
    have hu1 := (barHom_eq_one_iff hperf u').1 hb
    apply h.not_mem
    rw [Subgroup.mem_centralizer_iff]
    intro z hz'
    exact (hu1 ⟨z, hz'⟩).symm
  · intro x'
    have h1 := hcomm x'
    simp only [hg, Subgroup.coe_mul, Subgroup.coe_inv, hu'] at h1
    calc u * (x' : Y) * u⁻¹ = (y₀ : Y) * ((y₀ : Y)⁻¹ * u * (x' : Y)) * u⁻¹ := by group
      _ = (y₀ : Y) * ((x' : Y) * ((y₀ : Y)⁻¹ * u)) * u⁻¹ := by rw [h1]
      _ = (y₀ : Y) * x' * (y₀ : Y)⁻¹ := by group

theorem not_isComponentIn_of_fix_free (h : E68CentHyp L R u) (hfix : InvolFixInner (Qbar L))
    (hfree : ∀ t : Qbar L, orderOf t = 2 →
      ∀ B : Subgroup (centralizer ({t} : Set (Qbar L))), ¬ CFSG.IsComponent B)
    (K : Subgroup Y) : ¬ IsComponentIn K (L ⊓ centralizer ({u} : Set Y)) := by
  rintro ⟨hKH, hc⟩
  obtain ⟨y₀, hy₀, hact⟩ := exists_inner_lift h hfix
  set H : Subgroup Y := L ⊓ centralizer ({u} : Set Y) with hH
  have hKL : K ≤ L := hKH.trans inf_le_left
  have hiff : ∀ x : ↥L, (x : Y) ∈ centralizer ({u} : Set Y) ↔ x ∈ centralizer ({y₀} : Set ↥L) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have h1 := hact x
    constructor
    · intro hxu
      have h2 : u * (x : Y) * u⁻¹ = x := by rw [← hxu]; group
      rw [h2] at h1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      calc (x : Y) * y₀ = (y₀ * x * (y₀ : Y)⁻¹) * y₀ := by rw [← h1]
        _ = y₀ * x := by group
    · intro hxy
      have h2 : (y₀ : Y) * x * (y₀ : Y)⁻¹ = x := by
        have := congrArg Subtype.val hxy
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
        rw [← this]
        group
      rw [h2] at h1
      calc (x : Y) * u = (u * (x : Y) * u⁻¹) * u := by rw [h1]
        _ = u * x := by group
  have hKD : K.subgroupOf L ≤ centralizer ({y₀} : Set ↥L) := by
    intro x hx
    exact (hiff x).1 (Subgroup.mem_inf.mp (hKH (Subgroup.mem_subgroupOf.mp hx))).2
  have hq : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv ((subgroupOfEquivOfLe hKH).trans (subgroupOfEquivOfLe hKL).symm)
      hc.1
  let ψ : ↥(centralizer ({y₀} : Set ↥L)) →* ↥H :=
    { toFun := fun d => ⟨((d : ↥L) : Y), Subgroup.mem_inf.mpr ⟨(d : ↥L).2, (hiff d).2 d.2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hsub : ((K.subgroupOf L).subgroupOf (centralizer ({y₀} : Set ↥L))).IsSubnormal := by
    have h1 := hc.2.comap ψ
    convert h1 using 1
    ext x
    rfl
  exact false_of_component_of_centralizer hfree hy₀ hKD hq hsub

theorem not_isComponentIn_of_fixed_solvable (h : E68CentHyp L R u)
    (hfix : ∀ α : MulAut ↥L, α ^ 2 = 1 → α ≠ 1 → ∀ M : Subgroup ↥L,
      (∀ x ∈ M, α x = x) → Group.IsSolvable ↥M)
    (K : Subgroup Y) : ¬ IsComponentIn K (L ⊓ centralizer ({u} : Set Y)) := by
  rintro ⟨hKH, hc⟩
  set u' : ↥(normalizer (L : Set Y)) := ⟨u, h.normalizer h.mem⟩ with hu'
  have hu2 : u' * u' = 1 := Subtype.ext (by simpa [pow_two] using h.sq)
  have hα2 : conjL L u' ^ 2 = 1 := by rw [pow_two, ← conjL_mul, hu2, conjL_one]
  have hα1 : conjL L u' ≠ 1 := by
    intro h1
    apply h.not_mem
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨z, hz⟩ : ↥L) : Y)) h1
    simp only [conjL_apply, MulAut.one_apply] at h2
    have h3 : u * z = z * u := by
      calc u * z = (u * z * u⁻¹) * u := by group
        _ = z * u := by rw [h2]
    exact h3.symm
  have hsolv : Group.IsSolvable ↥((L ⊓ centralizer ({u} : Set Y)).subgroupOf L) := by
    refine hfix _ hα2 hα1 _ fun x hx => ?_
    have hx' : (x : Y) * u = u * (x : Y) :=
      mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
    apply Subtype.ext
    rw [conjL_apply]
    calc u * (x : Y) * u⁻¹ = (u * (x : Y)) * u⁻¹ := rfl
      _ = ((x : Y) * u) * u⁻¹ := by rw [← hx']
      _ = x := by group
  have hle : L ⊓ centralizer ({u} : Set Y) ≤ L := inf_le_left
  have hH : Group.IsSolvable ↥(L ⊓ centralizer ({u} : Set Y)) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (subgroupOfEquivOfLe hle).symm.injective
  exact not_isComponent_of_isSolvable _ hc

end Ambient

end CFSG.Quasithin.E6.Inn
