module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family Subgroup

section Rep

variable {Hg : Type*} [Group Hg] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem commSub_inv (σ : Hg →* (E ≃ₗ[ZMod 2] E)) {N : Subgroup Hg} {g : Hg}
    (hg : ∀ n ∈ N, g * n * g⁻¹ ∈ N) : ∀ x ∈ Family.commSub σ N, σ g x ∈ Family.commSub σ N := by
  intro x hx
  have hle : Family.commSub σ N ≤ (Family.commSub σ N).comap (σ g : E →ₗ[ZMod 2] E) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, hn, f, rfl⟩
    show σ g (σ n f - f) ∈ Family.commSub σ N
    have h1 : σ g (σ n f - f) = σ (g * n * g⁻¹) (σ g f) - σ g f := by
      rw [map_sub]
      congr 1
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        ← LinearEquiv.mul_apply (σ g⁻¹), ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [h1]
    exact Submodule.subset_span ⟨_, hg n hn, σ g f, rfl⟩
  exact hle hx

theorem commSub_subRep_eq_top (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) {N : Subgroup Hg}
    (hN : Group.IsPerfect ↥N) (hD : IsInvRep ρ (Family.commSub ρ N)) :
    Family.commSub (subRep ρ (Family.commSub ρ N) hD) N = ⊤ := by
  set D := Family.commSub ρ N with hDdef
  set ρD := subRep ρ D hD with hρD
  set D₂ := (Family.commSub ρD N).map D.subtype with hD₂
  have hgen : ∀ n ∈ N, ∀ d ∈ D, ρ n d - d ∈ D₂ := by
    intro n hn d hd
    refine ⟨ρD n ⟨d, hd⟩ - ⟨d, hd⟩, Submodule.subset_span ⟨n, hn, ⟨d, hd⟩, rfl⟩, ?_⟩
    rw [map_sub]
    rfl
  have hinv : IsInvRep (ρ.comp N.subtype) D₂ := by
    rintro g _ ⟨y, hy, rfl⟩
    have hg : ∀ n ∈ N, (g : Hg) * n * (g : Hg)⁻¹ ∈ N := fun n hn =>
      N.mul_mem (N.mul_mem g.2 hn) (N.inv_mem g.2)
    exact ⟨ρD g y, commSub_inv ρD hg y hy, rfl⟩
  set ρ' := quotRep (ρ.comp N.subtype) D₂ hinv with hρ'
  have h1 : ∀ g, ∀ x ∈ D.map D₂.mkQ, ρ' g x = x := by
    rintro g _ ⟨d, hd, rfl⟩
    show quotRep (ρ.comp N.subtype) D₂ hinv g (Submodule.Quotient.mk d) = Submodule.Quotient.mk d
    rw [quotRep_mk, Submodule.Quotient.eq]
    exact hgen g g.2 d hd
  have h2 : ∀ g x, ρ' g x - x ∈ D.map D₂.mkQ := by
    intro g x
    obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective D₂ x
    refine ⟨ρ g e - e, Submodule.subset_span ⟨g, g.2, e, rfl⟩, ?_⟩
    show Submodule.Quotient.mk (ρ g e - e) =
      quotRep (ρ.comp N.subtype) D₂ hinv g (Submodule.Quotient.mk e) - Submodule.Quotient.mk e
    rw [quotRep_mk, Submodule.Quotient.mk_sub]
    rfl
  have htriv := rep_trivial_of_sub_quot hN ρ' (D.map D₂.mkQ) h1 h2
  have hDD₂ : D ≤ D₂ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, hn, e, rfl⟩
    have h3 := htriv ⟨n, hn⟩ (Submodule.Quotient.mk e)
    rw [hρ', quotRep_mk, Submodule.Quotient.eq] at h3
    exact h3
  rw [eq_top_iff]
  rintro y -
  obtain ⟨z, hz, hzy⟩ := hDD₂ y.2
  have : z = y := Subtype.ext hzy
  rw [← this]
  exact hz

theorem finrank_sub_fixedSub_subRep_le [Module.Finite (ZMod 2) E]
    (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E) (hD : IsInvRep ρ D)
    (B : Subgroup Hg) :
    Module.finrank (ZMod 2) ↥D - Module.finrank (ZMod 2) ↥(Family.fixedSub (subRep ρ D hD) B) ≤
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) ↥(Family.fixedSub ρ B) := by
  set F := Family.fixedSub ρ B with hF
  let e : ↥(Family.fixedSub (subRep ρ D hD) B) ≃ₗ[ZMod 2] ↥(D ⊓ F) :=
    { toFun := fun x => ⟨((x : ↥D) : E), (x : ↥D).2, fun b hb =>
        congrArg Subtype.val (x.2 b hb)⟩
      invFun := fun y => ⟨⟨(y : E), y.2.1⟩, fun b hb => Subtype.ext (y.2.2 b hb)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq D F
  have h2 : Module.finrank (ZMod 2) ↥(D ⊔ F) ≤ Module.finrank (ZMod 2) E :=
    Submodule.finrank_le _
  have h3 : Module.finrank (ZMod 2) ↥(Family.fixedSub (subRep ρ D hD) B) =
      Module.finrank (ZMod 2) ↥(D ⊓ F) := e.finrank_eq
  omega

end Rep

section Groups

variable {X : Type*} [Group X]

theorem le_normalizer_center_map {L Y : Subgroup X} (hYL : Y ≤ normalizer (L : Set X)) :
    Y ≤ normalizer (((center ↥L).map L.subtype : Subgroup X) : Set X) := by
  have key : ∀ y ∈ normalizer (L : Set X), ∀ x ∈ (center ↥L).map L.subtype,
      y * x * y⁻¹ ∈ (center ↥L).map L.subtype := by
    rintro y hy _ ⟨c, hc, rfl⟩
    have hcy : y * (c : X) * y⁻¹ ∈ L := (mem_normalizer_iff.1 hy _).1 c.2
    have hc' : c ∈ center ↥L := hc
    refine ⟨⟨_, hcy⟩, ?_, rfl⟩
    show _ ∈ center ↥L
    rw [mem_center_iff] at hc' ⊢
    intro l
    have hl' : y⁻¹ * (l : X) * y ∈ L := by
      have := (mem_normalizer_iff.1 (inv_mem hy) (l : X)).1 l.2
      simpa using this
    have h1 : (y⁻¹ * (l : X) * y) * (c : X) = (c : X) * (y⁻¹ * (l : X) * y) :=
      congrArg (fun w : ↥L => (w : X)) (hc' ⟨_, hl'⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (l : X) * (y * (c : X) * y⁻¹) = y * ((y⁻¹ * (l : X) * y) * (c : X)) * y⁻¹ := by group
      _ = y * ((c : X) * (y⁻¹ * (l : X) * y)) * y⁻¹ := by rw [h1]
      _ = y * (c : X) * y⁻¹ * (l : X) := by group
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key y (hYL hy) x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem (hYL hy)) _ hx
  simpa [mul_assoc] using this

theorem eq_one_of_centralizes [Finite X] {Y L T₀ : Subgroup X} (hY : Y = L ⊔ T₀)
    (hT₀N : T₀ ≤ normalizer (L : Set X)) (hT₀ : IsPGroup 2 T₀) (hO : pCoreOf 2 Y = ⊥)
    (hZ : center ↥L = ⊥) :
    ∀ z : ↥Y, (∀ n ∈ L.subgroupOf Y, z * n = n * z) → z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : L ≤ Y := by rw [hY]; exact le_sup_left
  have hTY : T₀ ≤ Y := by rw [hY]; exact le_sup_right
  have hYN : Y ≤ normalizer (L : Set X) := by rw [hY]; exact sup_le le_normalizer hT₀N
  have hNn : (L.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hLY).2 hYN
  set C := centralizer (L.subgroupOf Y : Set ↥Y) with hC
  have h2 : ∀ c ∈ C, ∃ m : ℕ, c ^ 2 ^ m = 1 := by
    intro c hc
    have hcLT : (c : X) ∈ L ⊔ T₀ := by rw [← hY]; exact c.2
    obtain ⟨l, hl, t, ht, hlt⟩ := mem_sup_of_le_normalizer hT₀N hcLT
    obtain ⟨m, hm⟩ := hT₀ ⟨t, ht⟩
    have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
    refine ⟨m, ?_⟩
    have hq : QuotientGroup.mk' (L.subgroupOf Y) (c ^ 2 ^ m) = 1 := by
      have hc' : c = ⟨l, hLY hl⟩ * ⟨t, hTY ht⟩ := Subtype.ext hlt
      have hl1 : QuotientGroup.mk' (L.subgroupOf Y) ⟨l, hLY hl⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hl)
      have ht1 : (⟨t, hTY ht⟩ : ↥Y) ^ 2 ^ m = 1 := Subtype.ext (by
        simpa using hm')
      rw [map_pow, hc', map_mul, hl1, one_mul, ← map_pow, ht1, map_one]
    have hcL : c ^ 2 ^ m ∈ L.subgroupOf Y := (QuotientGroup.eq_one_iff _).1 hq
    have hcC : c ^ 2 ^ m ∈ C := C.pow_mem hc _
    have hcen : (⟨((c ^ 2 ^ m : ↥Y) : X), mem_subgroupOf.1 hcL⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro l'
      have h3 := mem_centralizer_iff.1 hcC ⟨l', hLY l'.2⟩ (mem_subgroupOf.2 l'.2)
      have h4 : (l' : X) * ((c ^ 2 ^ m : ↥Y) : X) = ((c ^ 2 ^ m : ↥Y) : X) * (l' : X) :=
        congrArg (fun w : ↥Y => (w : X)) h3
      exact Subtype.ext h4
    rw [hZ, mem_bot] at hcen
    have h5 : ((c ^ 2 ^ m : ↥Y) : X) = 1 := congrArg (fun w : ↥L => (w : X)) hcen
    exact Subtype.ext h5
  have hC2 : IsPGroup 2 ↥(C.map Y.subtype) := by
    rintro ⟨_, c, hc, rfl⟩
    obtain ⟨m, hm⟩ := h2 c hc
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
  have hCn : Y ≤ normalizer ((C.map Y.subtype : Subgroup X) : Set X) := by
    have hCnormal : C.Normal := Subgroup.normal_centralizer (H := L.subgroupOf Y)
    intro y hy
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨y, hy⟩ * c * ⟨y, hy⟩⁻¹, hCnormal.conj_mem c hc _, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      refine ⟨⟨y, hy⟩⁻¹ * c * ⟨y, hy⟩, ?_, ?_⟩
      · have := hCnormal.conj_mem c hc (⟨y, hy⟩⁻¹)
        simpa using this
      · have h4 : (c : X) = y * x * y⁻¹ := hcx
        show ((⟨y, hy⟩⁻¹ * c * ⟨y, hy⟩ : ↥Y) : X) = x
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h4]
        group
  have hle :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le C) hCn hC2
  rw [hO] at hle
  intro z hz
  have hzC : z ∈ C := mem_centralizer_iff.2 fun n hn => (hz n hn).symm
  have hz1 : (z : X) = 1 := (mem_bot).1 (hle ⟨z, hzC, rfl⟩)
  exact Subtype.ext hz1

end Groups

end CFSG.Quasithin.H13.A7
