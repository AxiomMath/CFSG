module

public import CFSG.Quasithin.Background.RonanE111Defs

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

section Transport

variable {G H : Type} [Group G] [Group H]

@[expose] def quotRestrict (φ : G →* H) (Mq : Subgroup H) : ↥(Mq.comap φ) →* ↥Mq :=
  (φ.comp (Mq.comap φ).subtype).codRestrict Mq fun x => x.2

theorem quotRestrict_surjective {φ : G →* H} (hφ : Function.Surjective φ) (Mq : Subgroup H) :
    Function.Surjective (quotRestrict φ Mq) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨⟨x, hy⟩, rfl⟩

theorem quotNormalComap (φ : G →* H) (Mq Kq : Subgroup H) [(Kq.subgroupOf Mq).Normal] :
    ((Kq.comap φ).subgroupOf (Mq.comap φ)).Normal := by
  have h : (Kq.comap φ).subgroupOf (Mq.comap φ) = (Kq.subgroupOf Mq).comap (quotRestrict φ Mq) :=
    Subgroup.ext fun x => Iff.rfl
  rw [h]
  exact (inferInstance : (Kq.subgroupOf Mq).Normal).comap (quotRestrict φ Mq)

theorem quotEquivOfSurj {φ : G →* H} (hφ : Function.Surjective φ) (Mq Kq : Subgroup H)
    [(Kq.subgroupOf Mq).Normal] [((Kq.comap φ).subgroupOf (Mq.comap φ)).Normal] :
    ∃ e : (↥(Mq.comap φ) ⧸ (Kq.comap φ).subgroupOf (Mq.comap φ)) ≃* (↥Mq ⧸ Kq.subgroupOf Mq),
      ∀ x : ↥(Mq.comap φ), e (QuotientGroup.mk x) = QuotientGroup.mk (quotRestrict φ Mq x) := by
  let ψ : ↥(Mq.comap φ) →* ↥Mq ⧸ Kq.subgroupOf Mq :=
    (QuotientGroup.mk' (Kq.subgroupOf Mq)).comp (quotRestrict φ Mq)
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (Kq.subgroupOf Mq)).comp (quotRestrict_surjective hφ Mq)
  have hker : ψ.ker = (Kq.comap φ).subgroupOf (Mq.comap φ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk (quotRestrict φ Mq x) : ↥Mq ⧸ Kq.subgroupOf Mq) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs), fun x => rfl⟩

theorem quotNormalizerComap (φ : G →* H) (Mq : Subgroup H) {t : G}
    (ht : φ t ∈ Subgroup.normalizer (Mq : Set H)) :
    t ∈ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at ht ⊢
  intro x
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact ht (φ x)

theorem quotNormalizerMap {φ : G →* H} (hφ : Function.Surjective φ) (Mq : Subgroup H) {s : G}
    (hs : s ∈ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G)) :
    φ s ∈ Subgroup.normalizer (Mq : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hs ⊢
  intro y
  obtain ⟨x, rfl⟩ := hφ y
  have hx := hs x
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv] at hx
  exact hx

open scoped Pointwise in
theorem quotSupMul {V U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V : Set G)) {x : G}
    (hx : x ∈ V ⊔ U) : ∃ v ∈ V, ∃ u ∈ U, x = v * u := by
  have hx' : x ∈ (V : Set G) * (U : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V U hUV]
    exact hx
  obtain ⟨v, hv, u, hu, rfl⟩ := hx'
  exact ⟨v, hv, u, hu, rfl⟩

theorem quotCongrApply {A B : Type} [Group A] [Group B] (e : A ≃* B) (α : MulAut A) (z : A) :
    MulAut.congr e α (e z) = e (α z) := by
  show e (α (e.symm (e z))) = e (α z)
  rw [MulEquiv.symm_apply_apply]

theorem quotCongrSymmApply {A B : Type} [Group A] [Group B] (e : A ≃* B) (α : MulAut B)
    (z : A) : e (((MulAut.congr e).symm α) z) = α (e z) := by
  show e (e.symm (α (e z))) = α (e z)
  exact e.apply_symm_apply _

theorem quotInduces {φ : G →* H} (hφ : Function.Surjective φ) (Mq Kq : Subgroup H)
    [(Kq.subgroupOf Mq).Normal] [((Kq.comap φ).subgroupOf (Mq.comap φ)).Normal]
    {e : (↥(Mq.comap φ) ⧸ (Kq.comap φ).subgroupOf (Mq.comap φ)) ≃* (↥Mq ⧸ Kq.subgroupOf Mq)}
    (he : ∀ x : ↥(Mq.comap φ), e (QuotientGroup.mk x) = QuotientGroup.mk (quotRestrict φ Mq x))
    {g : G} {α : MulAut (↥(Mq.comap φ) ⧸ (Kq.comap φ).subgroupOf (Mq.comap φ))}
    (hα : Induces (Mq.comap φ) (Kq.comap φ) g α) :
    Induces Mq Kq (φ g) (MulAut.congr e α) := by
  intro y
  obtain ⟨x, hx⟩ := hφ (y : H)
  have hxM : x ∈ Mq.comap φ := by
    rw [Subgroup.mem_comap, hx]
    exact y.2
  obtain ⟨x', hx'g, hx'α⟩ := hα ⟨x, hxM⟩
  have hx'g' : (x' : G) = g * x * g⁻¹ := hx'g
  refine ⟨⟨φ x', x'.2⟩, ?_, ?_⟩
  · show φ x' = φ g * (y : H) * (φ g)⁻¹
    rw [hx'g', map_mul, map_mul, map_inv, hx]
  · have hy' : quotRestrict φ Mq ⟨x, hxM⟩ = y := Subtype.ext hx
    have hy : (QuotientGroup.mk y : ↥Mq ⧸ Kq.subgroupOf Mq) = e (QuotientGroup.mk ⟨x, hxM⟩) := by
      rw [he, hy']
    rw [hy, quotCongrApply, hx'α, he]
    rfl

theorem quotInducesSymm {φ : G →* H} (hφ : Function.Surjective φ) (Mq Kq : Subgroup H)
    [(Kq.subgroupOf Mq).Normal] [((Kq.comap φ).subgroupOf (Mq.comap φ)).Normal]
    {e : (↥(Mq.comap φ) ⧸ (Kq.comap φ).subgroupOf (Mq.comap φ)) ≃* (↥Mq ⧸ Kq.subgroupOf Mq)}
    (he : ∀ x : ↥(Mq.comap φ), e (QuotientGroup.mk x) = QuotientGroup.mk (quotRestrict φ Mq x))
    {g : G} (hgM : g ∈ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G))
    {α' : MulAut (↥Mq ⧸ Kq.subgroupOf Mq)} (hα' : Induces Mq Kq (φ g) α') :
    Induces (Mq.comap φ) (Kq.comap φ) g ((MulAut.congr e).symm α') := by
  intro z
  have hmem : g * (z : G) * g⁻¹ ∈ Mq.comap φ :=
    (Subgroup.mem_normalizer_iff.mp hgM z).mp z.2
  refine ⟨⟨g * z * g⁻¹, hmem⟩, rfl, ?_⟩
  apply e.injective
  obtain ⟨w, hw1, hw2⟩ := hα' (quotRestrict φ Mq z)
  rw [quotCongrSymmApply, he, he, hw2]
  congr 1
  apply Subtype.ext
  show (w : H) = φ (g * z * g⁻¹)
  rw [hw1, map_mul, map_mul, map_inv]
  rfl

theorem quotFiniteMulAut (A : Type) [Group A] [Finite A] : Finite (MulAut A) :=
  Finite.of_injective (fun φ : MulAut A => (φ : A → A)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem quotNonabelian {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : B, a * b ≠ b * a) : ∃ a b : A, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
  simpa using congrArg e h'

theorem quotNParamMap [Finite G] [Finite H] {φ : G →* H} (hφ : Function.Surjective φ)
    (T : Subgroup G) (Mq Kq : Subgroup H) [(Kq.subgroupOf Mq).Normal]
    [((Kq.comap φ).subgroupOf (Mq.comap φ)).Normal] :
    E1.nParam (innAutInduced (T.map φ) Mq Kq) =
      E1.nParam (innAutInduced T (Mq.comap φ) (Kq.comap φ)) := by
  obtain ⟨e, he⟩ := quotEquivOfSurj hφ Mq Kq
  haveI := quotFiniteMulAut (↥(Mq.comap φ) ⧸ (Kq.comap φ).subgroupOf (Mq.comap φ))
  haveI := quotFiniteMulAut (↥Mq ⧸ Kq.subgroupOf Mq)
  have hSM : T ⊓ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) ⊓
      Subgroup.normalizer ((Kq.comap φ : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have hSbar : T.map φ ⊓ Subgroup.normalizer (Mq : Set H) ⊓ Subgroup.normalizer (Kq : Set H) ≤
      Subgroup.normalizer (Mq : Set H) :=
    fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have h1 : ∀ g ∈ Mq.comap φ ⊔ (T ⊓ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) ⊓
      Subgroup.normalizer ((Kq.comap φ : Subgroup G) : Set G)),
      ∃ g' ∈ Mq ⊔ (T.map φ ⊓ Subgroup.normalizer (Mq : Set H) ⊓ Subgroup.normalizer (Kq : Set H)),
        ∀ α, Induces (Mq.comap φ) (Kq.comap φ) g α → Induces Mq Kq g' (MulAut.congr e α) := by
    intro g hg
    obtain ⟨m, hm, s, hs, rfl⟩ := quotSupMul hSM hg
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hs
    obtain ⟨⟨hsT, hsM⟩, hsK⟩ := hs
    refine ⟨φ (m * s), ?_, fun α hα => quotInduces hφ Mq Kq he hα⟩
    rw [map_mul]
    exact Subgroup.mul_mem_sup hm (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_map_of_mem φ hsT, quotNormalizerMap hφ Mq hsM⟩, quotNormalizerMap hφ Kq hsK⟩)
  have h2 : ∀ g' ∈ Mq ⊔ (T.map φ ⊓ Subgroup.normalizer (Mq : Set H) ⊓ Subgroup.normalizer (Kq : Set H)),
      ∃ g ∈ Mq.comap φ ⊔ (T ⊓ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) ⊓
        Subgroup.normalizer ((Kq.comap φ : Subgroup G) : Set G)),
        ∀ α', Induces Mq Kq g' α' →
          Induces (Mq.comap φ) (Kq.comap φ) g ((MulAut.congr e).symm α') := by
    intro g' hg'
    obtain ⟨mq, hmq, sq, hsq, rfl⟩ := quotSupMul hSbar hg'
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hsq
    obtain ⟨⟨hsT, hsMq⟩, hsKq⟩ := hsq
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hsT
    obtain ⟨x, rfl⟩ := hφ mq
    have hxM : x ∈ Mq.comap φ := Subgroup.mem_comap.mpr hmq
    have htM : t ∈ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) :=
      quotNormalizerComap φ Mq hsMq
    have htK : t ∈ Subgroup.normalizer ((Kq.comap φ : Subgroup G) : Set G) :=
      quotNormalizerComap φ Kq hsKq
    have hxtM : x * t ∈ Subgroup.normalizer ((Mq.comap φ : Subgroup G) : Set G) :=
      mul_mem (Subgroup.le_normalizer hxM) htM
    refine ⟨x * t, Subgroup.mul_mem_sup hxM (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨ht, htM⟩, htK⟩), fun α' hα' => ?_⟩
    have hα'' : Induces Mq Kq (φ (x * t)) α' := by
      rw [map_mul]
      exact hα'
    exact quotInducesSymm hφ Mq Kq he hxtM hα''
  rw [innAutInduced_eq, innAutInduced_eq]
  exact nParam_closure_indSet_congr e h1 h2

end Transport

theorem HypT.quotient {G : Type} [Group G] [Finite G] {n : ℕ} {T N : Subgroup G} [N.Normal]
    (h : HypT n G T) : HypT n (G ⧸ N) (T.map (QuotientGroup.mk' N)) := by
  intro Mq Kq hKq hKqM hsn hTq hs hnab
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  haveI := quotNormalComap (QuotientGroup.mk' N) Mq Kq
  have hKM : Kq.comap (QuotientGroup.mk' N) ≤ Mq.comap (QuotientGroup.mk' N) :=
    Subgroup.comap_mono hKqM
  have hMsn : (Mq.comap (QuotientGroup.mk' N)).IsSubnormal := hsn.comap _
  have hTK : T ≤ Subgroup.normalizer ((Kq.comap (QuotientGroup.mk' N) : Subgroup G) : Set G) := by
    intro t ht
    exact quotNormalizerComap (QuotientGroup.mk' N) Kq
      (hTq (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) ht))
  obtain ⟨e, he⟩ := quotEquivOfSurj hsurj Mq Kq
  have hsM : IsSimpleGroup (↥(Mq.comap (QuotientGroup.mk' N)) ⧸
      (Kq.comap (QuotientGroup.mk' N)).subgroupOf (Mq.comap (QuotientGroup.mk' N))) :=
    (MulEquiv.isSimpleGroup_congr e).mpr hs
  have hnabM := quotNonabelian e hnab
  rw [quotNParamMap hsurj T Mq Kq]
  exact h (Mq.comap (QuotientGroup.mk' N)) (Kq.comap (QuotientGroup.mk' N)) hKM hMsn hTK hsM hnabM

end CFSG.Quasithin.RonanE111
