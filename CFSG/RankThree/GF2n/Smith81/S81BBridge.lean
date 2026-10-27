module

public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.RankThree.GF2n.Smith81.S81BSL2
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem finite_of_quadModel_equiv (ψ : M₀.E ≃ₗ[K] V) : Finite V := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  exact Finite.of_equiv M₀.E ψ.toEquiv

theorem Ctx.comm_mem_of_mem_QB {C : Subgroup G} (hC : Ctx M Q Z C) {t x : G} (ht : t ∈ QB C)
    (hx : x ∈ QB C) : ⁅t, x⁆ ∈ C := by
  obtain ⟨g, hg⟩ := hC.conj
  have hQB : QB C = conjSubgroup g Q := (Ctx.QB_eq hC hg).2
  have hQQ : ⁅Q, Q⁆ = Z := hC.hyp.special.1
  rw [hQB, mem_conjSubgroup] at ht
  rw [hQB, mem_conjSubgroup] at hx
  have hcomm : ⁅g⁻¹ * t * g, g⁻¹ * x * g⁆ ∈ ⁅Q, Q⁆ :=
    Subgroup.commutator_mem_commutator ht hx
  rw [hQQ] at hcomm
  rw [hg, mem_conjSubgroup]
  have heq : g⁻¹ * ⁅t, x⁆ * g = ⁅g⁻¹ * t * g, g⁻¹ * x * g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact hcomm

theorem quadModel_pi_one (M₀ : Tim79.QuadModel Q Z K γ) : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem quadModel_pi_inv (M₀ : Tim79.QuadModel Q Z K γ) {x : G} (hx : x ∈ Q) :
    M₀.π x⁻¹ = - M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, quadModel_pi_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

@[expose] noncomputable def psiHom (ψ : M₀.E ≃ₗ[K] V) : ↥Q →* Multiplicative V where
  toFun x := Multiplicative.ofAdd (ψ (M₀.π (x : G)))
  map_one' := by
    show Multiplicative.ofAdd (ψ (M₀.π 1)) = 1
    rw [quadModel_pi_one, map_zero]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (ψ (M₀.π ((x : G) * y))) =
      Multiplicative.ofAdd (ψ (M₀.π x)) * Multiplicative.ofAdd (ψ (M₀.π y))
    rw [M₀.π_mul x.1 x.2 y.1 y.2, map_add]
    rfl

theorem psiHom_apply (ψ : M₀.E ≃ₗ[K] V) (x : ↥Q) :
    Multiplicative.toAdd (psiHom ψ x) = ψ (M₀.π (x : G)) := rfl

theorem psiHom_eq_one_iff (ψ : M₀.E ≃ₗ[K] V) (x : ↥Q) : psiHom ψ x = 1 ↔ (x : G) ∈ Z := by
  rw [← (M₀.π_ker x.1 x.2)]
  constructor
  · intro h
    have h1 : ψ (M₀.π (x : G)) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa [psiHom_apply] using this
    exact ψ.injective (by rw [h1, map_zero])
  · intro h
    show Multiplicative.ofAdd (ψ (M₀.π (x : G))) = 1
    rw [h, map_zero]
    rfl

theorem psiHom_surjective (ψ : M₀.E ≃ₗ[K] V) : Function.Surjective (psiHom ψ) := by
  intro v
  obtain ⟨x, hx, hxv⟩ := M₀.π_surj (ψ.symm (Multiplicative.toAdd v))
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  show ψ (M₀.π x) = Multiplicative.toAdd v
  rw [hxv]
  simp

theorem EGeom.EUniData.psi_mem_Wsp (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {C : Subgroup G}
    (hC : Ctx M Q Z C) {g : V ≃ₗ[K] V}
    (himg : (fun a : G => ψ (M₀.π a)) '' (C : Set G) = (Submodule.span K {g p₀} : Set V))
    (hrad : ∀ u ∈ conjSub g U₀, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB C ∧ φ t = u)
    {x : G} (hx : x ∈ Q ⊓ QB C) :
    ψ (M₀.π x) ∈ Wsp (Submodule.span K {g p₀}) (conjSub g U₀) := by
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [mem_Wsp]
  intro u hu
  obtain ⟨t, htQB, htu⟩ := hrad u hu
  have hcC : ⁅(t : G), x⁆ ∈ C := Ctx.comm_mem_of_mem_QB hC htQB hxC
  have hcQ : ⁅(t : G), x⁆ ∈ Q := hC.le hcC
  have hkey : (t : G) * x * (t : G)⁻¹ = ⁅(t : G), x⁆ * x := by
    simp only [commutatorElement_def]
    group
  have heq := d.equivariant t x hxQ
  rw [hkey, M₀.π_mul _ hcQ x hxQ, htu, map_add] at heq
  have hmem : ψ (M₀.π ⁅(t : G), x⁆) ∈ Submodule.span K {g p₀} := by
    have h : ψ (M₀.π ⁅(t : G), x⁆) ∈ (Submodule.span K {g p₀} : Set V) := by
      rw [← himg]
      exact ⟨⁅(t : G), x⁆, SetLike.mem_coe.mpr hcC, rfl⟩
    exact SetLike.mem_coe.mp h
  have hdiff : u (ψ (M₀.π x)) - ψ (M₀.π x) = ψ (M₀.π ⁅(t : G), x⁆) := by
    rw [← heq]
    abel
  rw [hdiff]
  exact hmem

theorem EGeom.EUniData.exists_mem_inf_of_mem_Wsp (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀)
    {C : Subgroup G}
    (hC : Ctx M Q Z C) {g : V ≃ₗ[K] V}
    (himg : (fun a : G => ψ (M₀.π a)) '' (C : Set G) = (Submodule.span K {g p₀} : Set V))
    (hrad : ∀ u ∈ conjSub g U₀, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB C ∧ φ t = u)
    {n : ℕ} (hcard : Nat.card ↥(Q ⊓ QB C) = Nat.card Z ^ (n + 1))
    (hW : Nat.card (Wsp (Submodule.span K {p₀}) U₀) ≤ Nat.card K ^ n)
    (hK : Nat.card K = Nat.card Z) :
    ∀ v ∈ Wsp (Submodule.span K {g p₀}) (conjSub g U₀), ∃ x ∈ Q ⊓ QB C, ψ (M₀.π x) = v := by
  have hTQ : ∀ x : G, x ∈ Q ⊓ QB C → x ∈ Q := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hZT : Z ≤ Q ⊓ QB C := le_inf hC.Z_le_Q hC.Z_le_QB.1
  have hpos : 0 < Nat.card Z := by
    haveI : Nonempty ↥Z := ⟨⟨1, Z.one_mem⟩⟩
    exact Nat.card_pos
  obtain ⟨f, hf⟩ : ∃ f : ↥(Q ⊓ QB C) →* Multiplicative V,
      ∀ x : ↥(Q ⊓ QB C), f x = Multiplicative.ofAdd (ψ (M₀.π (x : G))) := by
    refine ⟨{ toFun := fun x => Multiplicative.ofAdd (ψ (M₀.π (x : G)))
              map_one' := ?_
              map_mul' := ?_ }, fun x => rfl⟩
    · have h1 : M₀.π 1 = 0 := (M₀.π_ker 1 Q.one_mem).mpr Z.one_mem
      show Multiplicative.ofAdd (ψ (M₀.π 1)) = 1
      rw [h1, map_zero]
      rfl
    · intro x y
      have h1 := M₀.π_mul (x : G) (hTQ _ x.2) (y : G) (hTQ _ y.2)
      show Multiplicative.ofAdd (ψ (M₀.π ((x : G) * (y : G))))
        = Multiplicative.ofAdd (ψ (M₀.π (x : G))) * Multiplicative.ofAdd (ψ (M₀.π (y : G)))
      rw [h1, map_add]
      rfl
  have hker : f.ker = Z.subgroupOf (Q ⊓ QB C) := by
    ext x
    rw [MonoidHom.mem_ker, hf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ψ (M₀.π (x : G)) = 0 := congrArg Multiplicative.toAdd h
      have h2 : M₀.π (x : G) = 0 := by simpa using h1
      exact (M₀.π_ker _ (hTQ _ x.2)).mp h2
    · intro hx
      have h2 : M₀.π (x : G) = 0 := (M₀.π_ker _ (hTQ _ x.2)).mpr hx
      show Multiplicative.ofAdd (ψ (M₀.π (x : G))) = 1
      rw [h2, map_zero]
      rfl
  have hkerCard : Nat.card f.ker = Nat.card Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZT).toEquiv
  have hrange : Nat.card f.range = Nat.card Z ^ n := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hkerCard, hcard] at h
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h, pow_succ']
  have himg' : Multiplicative.toAdd '' (f.range : Set (Multiplicative V))
      = {v | ∃ x ∈ Q ⊓ QB C, ψ (M₀.π x) = v} := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (SetLike.mem_coe.mp hy)
      refine ⟨(x : G), x.2, ?_⟩
      rw [hf]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨f ⟨x, hx⟩, SetLike.mem_coe.mpr (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩), ?_⟩
      rw [hf]
      rfl
  have hScard : {v | ∃ x ∈ Q ⊓ QB C, ψ (M₀.π x) = v}.ncard = Nat.card K ^ n := by
    rw [← himg', Set.ncard_image_of_injective _ Multiplicative.toAdd.injective, hK, ← hrange]
    exact (Nat.card_coe_set_eq _).symm
  have hWcard : (Wsp (Submodule.span K {g p₀}) (conjSub g U₀) : Set V).ncard ≤
      Nat.card K ^ n := by
    have hWeq : (Wsp (Submodule.span K {g p₀}) (conjSub g U₀) : Set V).ncard
        = Nat.card (Wsp (Submodule.span K {g p₀}) (conjSub g U₀)) :=
      (Nat.card_coe_set_eq _).symm
    have hspan : Submodule.span K {g p₀} = (Submodule.span K {p₀}).map (g : V →ₗ[K] V) := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    rw [hWeq, hspan, card_Wsp_conj g (Submodule.span K {p₀}) U₀]
    exact hW
  intro v hv
  haveI : Finite V := finite_of_quadModel_equiv ψ
  have hSW : {v | ∃ x ∈ Q ⊓ QB C, ψ (M₀.π x) = v}
      ⊆ (Wsp (Submodule.span K {g p₀}) (conjSub g U₀) : Set V) := by
    rintro v ⟨x, hx, rfl⟩
    exact EUniData.psi_mem_Wsp d hC himg hrad hx
  have hEq : {v | ∃ x ∈ Q ⊓ QB C, ψ (M₀.π x) = v}
      = (Wsp (Submodule.span K {g p₀}) (conjSub g U₀) : Set V) :=
    Set.eq_of_subset_of_ncard_le hSW (by rw [hScard]; exact hWcard)
  have hvS : v ∈ {v | ∃ x ∈ Q ⊓ QB C, ψ (M₀.π x) = v} := by
    rw [hEq]
    exact hv
  obtain ⟨x, hx, hxv⟩ := hvS
  exact ⟨x, hx, hxv⟩

theorem EGeom.EUniData.exists_ctx_point (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (hB : Ctx M Q Z B)
    (hp₀ : p₀ ≠ 0) {h : V ≃ₗ[K] V} (hh : h ∈ Γ) :
    ∃ D : Subgroup G, Ctx M Q Z D ∧
      (fun a : G => ψ (M₀.π a)) '' (D : Set G) = (Submodule.span K {h p₀} : Set V) := by
  obtain ⟨gB, hgBΓ, himgB, -⟩ := d.point B hB.conj hB.le hB.ne
  obtain ⟨g, hg⟩ := hB.conj
  have hmem : h * gB⁻¹ ∈ φ.range := by
    rw [d.range]
    exact Γ.mul_mem hh (Γ.inv_mem hgBΓ)
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hmem
  have hnorm : ∀ x : G, x ∈ Q ↔ (s : G) * x * (s : G)⁻¹ ∈ Q :=
    fun x => Subgroup.mem_normalizer_iff.mp (d.le_normalizer s.2) x
  have hDQ : conjSubgroup (s : G) B ≤ Q := by
    intro x hx
    have hb : (s : G)⁻¹ * x * (s : G) ∈ B := mem_conjSubgroup.mp hx
    have key : (s : G) * ((s : G)⁻¹ * x * (s : G)) * (s : G)⁻¹ ∈ Q :=
      (hnorm _).mp (hB.le hb)
    have e : (s : G) * ((s : G)⁻¹ * x * (s : G)) * (s : G)⁻¹ = x := by group
    rwa [e] at key
  have hDconj : conjSubgroup (s : G) B = conjSubgroup ((s : G) * g) Z :=
    (congrArg (conjSubgroup (s : G)) hg).trans (conjSubgroup_mul (s : G) g Z).symm
  have himgD : (fun a : G => ψ (M₀.π a)) '' ((conjSubgroup (s : G) B : Subgroup G) : Set G) =
      φ s '' ((fun a : G => ψ (M₀.π a)) '' ((B : Subgroup G) : Set G)) := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ conjSubgroup (s : G) B := hy
      have hb : (s : G)⁻¹ * y * (s : G) ∈ B := mem_conjSubgroup.mp hy'
      have e : (s : G) * ((s : G)⁻¹ * y * (s : G)) * (s : G)⁻¹ = y := by group
      refine ⟨ψ (M₀.π ((s : G)⁻¹ * y * (s : G))), ⟨(s : G)⁻¹ * y * (s : G), hb, rfl⟩, ?_⟩
      show φ s (ψ (M₀.π ((s : G)⁻¹ * y * (s : G)))) = ψ (M₀.π y)
      rw [← d.equivariant s _ (hB.le hb), e]
    · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨(s : G) * b * (s : G)⁻¹, ?_, d.equivariant s b (hB.le hb)⟩
      have e : (s : G)⁻¹ * ((s : G) * b * (s : G)⁻¹) * (s : G) = b := by group
      rw [SetLike.mem_coe, mem_conjSubgroup, e]
      exact hb
  have himgφ : φ s '' ((Submodule.span K {gB p₀} : Submodule K V) : Set V) =
      ((Submodule.span K {φ s (gB p₀)} : Submodule K V) : Set V) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : w ∈ Submodule.span K {gB p₀} := hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw'
      exact Submodule.mem_span_singleton.mpr ⟨a, by rw [map_smul]⟩
    · intro hv
      have hv' : v ∈ Submodule.span K {φ s (gB p₀)} := hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv'
      exact ⟨a • gB p₀, Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _),
        by rw [map_smul]⟩
  have hφ : φ s (gB p₀) = h p₀ := by
    rw [hs]
    simp
  have himgFinal : (fun a : G => ψ (M₀.π a)) '' ((conjSubgroup (s : G) B : Subgroup G) : Set G) =
      ((Submodule.span K {h p₀} : Submodule K V) : Set V) := by
    rw [himgD, himgB, himgφ, hφ]
  have hne : conjSubgroup (s : G) B ≠ Z := by
    intro hDZ
    have hmemZ : h p₀ ∈
        (fun a : G => ψ (M₀.π a)) '' ((conjSubgroup (s : G) B : Subgroup G) : Set G) := by
      rw [himgFinal]
      exact SetLike.mem_coe.mpr (Submodule.mem_span_singleton_self _)
    rw [hDZ] at hmemZ
    obtain ⟨z, hz, hzeq⟩ := hmemZ
    have hzQ : z ∈ Q := hB.hyp.Z_normal.1 hz
    have hz0 : M₀.π z = 0 := (M₀.π_ker z hzQ).mpr hz
    have hz2 : ψ (M₀.π z) = h p₀ := hzeq
    rw [hz0, map_zero] at hz2
    exact hp₀ ((LinearEquiv.map_eq_zero_iff h).mp hz2.symm)
  exact ⟨conjSubgroup (s : G) B, ⟨hB.hyp, ⟨(s : G) * g, hDconj⟩, hDQ, hne⟩, himgFinal⟩

theorem natCard_comap_eq_mul_ker {H H' : Type} [Group H] [Group H'] [Finite H]
    (f : H →* H') (hf : Function.Surjective f) (T : Subgroup H') :
    Nat.card (T.comap f) = Nat.card T * Nat.card f.ker := by
  have h1 : Nat.card (T.comap f) * T.index = Nat.card H := by
    rw [← Subgroup.index_comap_of_surjective (H := T) hf]
    exact Subgroup.card_mul_index _
  have h2 : Nat.card T * T.index = Nat.card H' := Subgroup.card_mul_index T
  have h3 : Nat.card f.ker * Nat.card H' = Nat.card H :=
    Subgroup.card_ker_mul_card_of_surjective (f := f) hf
  have hi : T.index ≠ 0 := by
    intro h0
    have hpos : 0 < Nat.card H := Nat.card_pos
    rw [h0, mul_zero] at h1
    omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1, ← h3, ← h2]
  ring

theorem card_psi_preimage (ψ : M₀.E ≃ₗ[K] V) [Finite G] (P : Submodule K V) (hZQ : Z ≤ Q) :
    Nat.card {x : G // ∃ _ : x ∈ Q, ψ (M₀.π x) ∈ P} = Nat.card Z * Nat.card P := by
  have hker : (psiHom ψ).ker = Z.subgroupOf Q := by
    ext y
    rw [MonoidHom.mem_ker, psiHom_eq_one_iff, Subgroup.mem_subgroupOf]
  have hZ : Nat.card (psiHom ψ).ker = Nat.card Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv
  have hT : Nat.card (P.toAddSubgroup.toSubgroup) = Nat.card P :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun a => Iff.rfl))
  have hcomap := natCard_comap_eq_mul_ker (psiHom ψ) (psiHom_surjective ψ)
    P.toAddSubgroup.toSubgroup
  have hequiv : {x : G // ∃ _ : x ∈ Q, ψ (M₀.π x) ∈ P} ≃
      ↥((P.toAddSubgroup.toSubgroup).comap (psiHom ψ)) :=
    (Equiv.subtypeSubtypeEquivSubtypeExists (fun x : G => x ∈ Q)
        (fun y : ↥Q => ψ (M₀.π (y : G)) ∈ P)).symm.trans
      (Equiv.subtypeEquivRight (fun y => by
        rw [Subgroup.mem_comap, Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup,
          psiHom_apply]))
  rw [Nat.card_congr hequiv, hcomap, hT, hZ, Nat.mul_comm]

theorem card_span_pair [Finite K] [Finite V] {c r : V} (hc : c ≠ 0)
    (hr : r ∉ Submodule.span K {c}) : Nat.card (Submodule.span K {c, r}) = Nat.card K ^ 2 := by
  have hli : LinearIndependent K ![c, r] := by
    rw [LinearIndependent.pair_iff' hc]
    intro a ha
    apply hr
    rw [← ha]
    exact (Submodule.span K {c}).smul_mem a (Submodule.mem_span_singleton_self c)
  have hrange : Set.range ![c, r] = ({c, r} : Set V) := Matrix.range_cons_cons_empty c r _
  have hfin : Module.finrank K (Submodule.span K ({c, r} : Set V)) = 2 := by
    have h := finrank_span_eq_card hli
    rw [hrange, Fintype.card_fin] at h
    exact h
  haveI : Module.Finite K (Submodule.span K ({c, r} : Set V)) :=
    FiniteDimensional.span_of_finite K (Set.toFinite ({c, r} : Set V))
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(Submodule.span K ({c, r} : Set V))), hfin]

theorem exists_S_of_uniform (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {n : ℕ} (hG : MinuscGeom Γ p₀ U₀ n)
    (hB : Ctx M Q Z B) (hw : Width Q Z n) (h34 : Stroth34Statement) (hn : 2 < n)
    (hno : ∀ C, Ctx M Q Z C → NoA2 Q Z (LB M Q C)) (hgen : ∀ C, Ctx M Q Z C → GenByB M Q C)
    {C : Subgroup G} (hC : Ctx M Q Z C) :
    ∃ S : Subgroup G, S ≤ Q ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → InZClass Z s) ∧
      Nat.card Z ^ 2 < Nat.card S := by
  classical
  have hH : StrothHyp M Q Z := hB.hyp
  obtain ⟨gC, hgCΓ, himgC, hradC⟩ := d.point C hC.conj hC.le hC.ne
  obtain ⟨g₁, hg₁Γ, hg₁W, hg₁n, hplane⟩ := hG.line
  haveI : Finite V := finite_of_quadModel_equiv ψ
  have hcard : Nat.card ↥(Q ⊓ QB C) = Nat.card Z ^ (n + 1) :=
    (stroth_3_5 h34 hC hw hn (hno C hC) (hgen C hC)).2.2.2
  have hcover := d.exists_mem_inf_of_mem_Wsp hC himgC hradC hcard hG.W_le hg.card
  set c : V := gC p₀ with hc
  set r : V := gC (g₁ p₀) with hr
  set W : Submodule K V := Wsp (Submodule.span K {c}) (conjSub gC U₀) with hWdef
  have hcW : c ∈ W := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.mp hu
    have hfix : u₀ p₀ = p₀ := hG.U₀_fix u₀ hu₀
    have hinv : gC⁻¹ (gC p₀) = p₀ := by simp
    have : (gC * u₀ * gC⁻¹) c - c = 0 := by
      rw [hc, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, hfix, sub_self]
    rw [this]; exact Submodule.zero_mem _
  have hrW : r ∈ W := by
    have hmap : (Submodule.span K {p₀}).map (gC : V →ₗ[K] V) = Submodule.span K {c} := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    have h := Submodule.mem_map_of_mem (f := (gC : V →ₗ[K] V)) hg₁W
    rw [← Wsp_map, hmap] at h
    exact h
  have hc0 : c ≠ 0 := fun h => hG.p₀_ne (gC.injective (by rw [map_zero]; exact h))
  have hrc : r ∉ Submodule.span K {c} := by
    intro h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    apply hg₁n
    refine Submodule.mem_span_singleton.mpr ⟨t, gC.injective ?_⟩
    rw [map_smul]
    exact ht
  let P : Submodule K V := Submodule.span K {c, r}
  have hPW : P ≤ W := Submodule.span_le.mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact hcW
    · exact hrW)
  let S : Subgroup G :=
    { carrier := {x | ∃ _ : x ∈ Q, ψ (M₀.π x) ∈ P}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨haQ, hpa⟩ := ha
        obtain ⟨hbQ, hpb⟩ := hb
        exact ⟨Q.mul_mem haQ hbQ, by rw [M₀.π_mul a haQ b hbQ, map_add]; exact P.add_mem hpa hpb⟩
      one_mem' := ⟨Q.one_mem, by rw [quadModel_pi_one, map_zero]; exact P.zero_mem⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨haQ, hpa⟩ := ha
        exact ⟨Q.inv_mem haQ, by rw [quadModel_pi_inv M₀ haQ, map_neg]; exact P.neg_mem hpa⟩ }
  have hmemS : ∀ x, x ∈ S ↔ ∃ _ : x ∈ Q, ψ (M₀.π x) ∈ P := fun x => Iff.rfl
  refine ⟨S, ?_, ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨hxQ, hxP⟩ := (hmemS x).mp hx
    obtain ⟨y, hy, hyx⟩ := hcover _ (hPW hxP)
    have hyQ : y ∈ Q := hy.1
    have hxy : x * y⁻¹ ∈ Z := by
      rw [← M₀.π_ker (x * y⁻¹) (Q.mul_mem hxQ (Q.inv_mem hyQ)), M₀.π_mul x hxQ _ (Q.inv_mem hyQ),
        quadModel_pi_inv M₀ hyQ, ← sub_eq_add_neg]
      apply ψ.injective
      rw [map_sub, hyx, map_zero, sub_self]
    have hZC : Z ≤ QB C := hC.Z_le_QB.1
    refine ⟨hxQ, ?_⟩
    have : x = (x * y⁻¹) * y := by group
    rw [this]
    exact (QB C).mul_mem (hZC hxy) hy.2
  ·
    intro s hs hs1
    obtain ⟨hsQ, hsP⟩ := (hmemS s).mp hs
    by_cases hsZ : s ∈ Z
    · exact ⟨1, s, hsZ, hs1, by simp⟩
    have hψ0 : ψ (M₀.π s) ≠ 0 := fun h0 =>
      hsZ ((M₀.π_ker s hsQ).mp (ψ.injective (h0.trans (map_zero ψ).symm)))
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hsP
    have hab0 : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hcon
      simp only [not_or, ne_eq, not_not] at hcon
      apply hψ0
      rw [← hab, hcon.1, hcon.2, zero_smul, zero_smul, add_zero]
    obtain ⟨h', hh'Γ, hh'p⟩ := hplane a b hab0
    have hgh : (gC * h') p₀ = ψ (M₀.π s) := by
      rw [← hab, LinearEquiv.mul_apply, hh'p, map_add, map_smul, map_smul]
    obtain ⟨D, hD, hDim⟩ := d.exists_ctx_point hB hG.p₀_ne (Γ.mul_mem hgCΓ hh'Γ)
    have hmem : ψ (M₀.π s) ∈ (fun a : G => ψ (M₀.π a)) '' (D : Set G) := by
      rw [hDim, ← hgh]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨y, hyD, hyeq⟩ := hmem
    have hyeq' : ψ (M₀.π y) = ψ (M₀.π s) := hyeq
    have hyQ : y ∈ Q := hD.le hyD
    have hsyZ : s * y⁻¹ ∈ Z := by
      rw [← M₀.π_ker (s * y⁻¹) (Q.mul_mem hsQ (Q.inv_mem hyQ)),
        M₀.π_mul s hsQ _ (Q.inv_mem hyQ), quadModel_pi_inv M₀ hyQ, ← sub_eq_add_neg]
      apply ψ.injective
      rw [map_sub, hyeq', map_zero, sub_self]
    have hsZD : s ∈ Z ⊔ D := by
      have hyD' : y ∈ D := hyD
      have h1 : s * y⁻¹ * y ∈ Z ⊔ D := Subgroup.mul_mem_sup hsyZ hyD'
      rwa [inv_mul_cancel_right] at h1
    exact Ctx.inZClass_of_mem_sup hD hsZD hs1
  ·
    have h1 : Nat.card ↥S = Nat.card Z * Nat.card P := by
      rw [← card_psi_preimage ψ P hH.Z_normal.1]
      exact Nat.card_congr (Equiv.subtypeEquivRight hmemS)
    have h2 : Nat.card P = Nat.card K ^ 2 := card_span_pair hc0 hrc
    have hq : 4 ≤ Nat.card Z := hH.q4
    rw [h1, h2, hg.card]
    nlinarith [Nat.pos_of_ne_zero (by omega : Nat.card Z ≠ 0)]

end CFSG.RankThree.GF2n.Smith81
