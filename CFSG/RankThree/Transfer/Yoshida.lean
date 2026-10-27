module

public import CFSG.RankThree.Transfer.Control
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.Transfer

open CFSG.GH74.GLS

section Residual

variable {X : Type*} [Group X]

instance oResidual_normal (p : ℕ) (X : Type*) [Group X] : (oResidual p X).Normal where
  conj_mem n hn g := by
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      change Nat.Coprime (orderOf (g * x * g⁻¹)) p
      have h := orderOf_conj g⁻¹ x
      rw [inv_inv] at h
      rw [h]
      exact hx
    | one => simp
    | mul x y _ _ hx hy =>
      have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ hx

theorem oResidual_le_ker_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    (f : X →* H) (hH : IsPGroup p H) : oResidual p X ≤ f.ker := by
  rw [oResidual, Subgroup.closure_le]
  intro x hx
  change f x = 1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hH) (f x)
  have hcop : Nat.Coprime (orderOf (f x)) (orderOf x) := by
    rw [hk]
    exact (Nat.Coprime.symm hx).pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_map_dvd f x))

theorem isPGroup_quotient_of_oResidual_le [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (L : Subgroup X) [L.Normal] (hL : oResidual p X ≤ L) : IsPGroup p (X ⧸ L) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.out.one_lt.ne'
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply hL
  apply Subgroup.subset_closure
  change Nat.Coprime (orderOf (x ^ p ^ a)) p
  rw [orderOf_pow_of_dvd (pow_ne_zero a hp.out.ne_zero) (Dvd.intro _ hord.symm), hord,
    Nat.mul_div_cancel_left m (pow_pos hp.out.pos a)]
  exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))

theorem map_mk_eq_top_of_isPGroup [Finite X] {p : ℕ} [Fact p.Prime] (P : Sylow p X)
    (L : Subgroup X) [L.Normal] (hL : IsPGroup p (X ⧸ L)) :
    (P : Subgroup X).map (QuotientGroup.mk' L) = ⊤ := by
  obtain ⟨k, hk⟩ := hL.index ((P : Subgroup X).map (QuotientGroup.mk' L))
  have hdvd := Subgroup.index_map_dvd (P : Subgroup X) (QuotientGroup.mk'_surjective L)
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact P.not_dvd_index ((dvd_pow_self p hk0).trans hdvd)
  rw [hk0, pow_zero] at hk
  exact Subgroup.index_eq_one.mp hk

end Residual

theorem forall_isEmpty_iff_not_exists {Q W : Type*} [Group Q] [Group W] :
    (∀ (K : Subgroup Q) [K.Normal], IsEmpty (Q ⧸ K ≃* W)) ↔
      ¬ ∃ (K : Subgroup Q) (_ : K.Normal), Nonempty (Q ⧸ K ≃* W) := by
  constructor
  · rintro h ⟨K, hK, ⟨e⟩⟩
    exact (h K).false e
  · intro h K _
    exact ⟨fun e => h ⟨K, inferInstance, ⟨e⟩⟩⟩

variable {G : Type*} [Group G]

theorem commutator_sup_oResidual_le_comap (p : ℕ) (X : Subgroup G) :
    commutator X ⊔ oResidual p X ≤ (commutator G ⊔ oResidual p G).comap X.subtype := by
  apply sup_le
  · rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator, commutator_def]
    exact le_sup_of_le_left (Subgroup.commutator_mono le_top le_top)
  · rw [← Subgroup.map_le_iff_le_comap]
    refine le_sup_of_le_right ?_
    rw [oResidual, MonoidHom.map_closure, oResidual]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    change Nat.Coprime (orderOf (x : G)) p
    rw [Subgroup.orderOf_coe]
    exact hx

@[expose] noncomputable def abelianPQuotientMap (p : ℕ) (X : Subgroup G) :
    X ⧸ (commutator X ⊔ oResidual p X) →* G ⧸ (commutator G ⊔ oResidual p G) :=
  QuotientGroup.map _ _ X.subtype (commutator_sup_oResidual_le_comap p X)

theorem abelianPQuotientMap_mk (p : ℕ) (X : Subgroup G) (x : X) :
    abelianPQuotientMap p X (x : X ⧸ (commutator X ⊔ oResidual p X)) = ((x : G) : G ⧸ _) :=
  rfl

variable [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)

local notation "N" => Subgroup.normalizer (((P : Sylow p G) : Subgroup G) : Set G)

theorem inf_commutator_sup_oResidual_le :
    (P : Subgroup G) ⊓ (commutator G ⊔ oResidual p G) ≤ commutator G := by
  have hle : commutator G ⊔ oResidual p G ≤ (P : Subgroup G).transferFocal.ker :=
    sup_le (Abelianization.commutator_subset_ker _)
      (oResidual_le_ker_of_isPGroup _ (P.isPGroup'.to_quotient _))
  calc (P : Subgroup G) ⊓ (commutator G ⊔ oResidual p G)
      ≤ (P : Subgroup G).transferFocal.ker ⊓ P := by
        rw [inf_comm]
        exact inf_le_inf_right _ hle
    _ = (P : Subgroup G).focalSubgroup := Subgroup.ker_transferFocal_inf_eq_focalSubgroup P
    _ ≤ commutator G := Subgroup.focalSubgroup_le_commutator _

theorem bijective_abelianPQuotientMap_of_inf_eq
    (h : (P : Subgroup G) ⊓ commutator G =
      (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N)) :
    Function.Bijective (abelianPQuotientMap p N) := by
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  constructor
  · rw [injective_iff_map_eq_one]
    intro x hx
    set PN : Sylow p N := P.subtype hPN
    have hNp : IsPGroup p (N ⧸ (commutator N ⊔ oResidual p N)) :=
      isPGroup_quotient_of_oResidual_le _ le_sup_right
    have htop := map_mk_eq_top_of_isPGroup PN _ hNp
    obtain ⟨w, hw, rfl⟩ := htop ▸ Subgroup.mem_top x
    have hwP : (w : G) ∈ (P : Subgroup G) := mem_of_mem_sylow_subtype P hw
    rw [QuotientGroup.mk'_apply, abelianPQuotientMap_mk, QuotientGroup.eq_one_iff] at hx
    have hwG : (w : G) ∈ (P : Subgroup G) ⊓ commutator G :=
      ⟨hwP, inf_commutator_sup_oResidual_le P ⟨hwP, hx⟩⟩
    rw [h] at hwG
    obtain ⟨w', hw', hww'⟩ := hwG.2
    have : w' = w := Subtype.ext hww'
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_sup_left (this ▸ hw')
  · intro y
    have hGp : IsPGroup p (G ⧸ (commutator G ⊔ oResidual p G)) :=
      isPGroup_quotient_of_oResidual_le _ le_sup_right
    have htop := map_mk_eq_top_of_isPGroup P _ hGp
    obtain ⟨a, ha, rfl⟩ := htop ▸ Subgroup.mem_top y
    exact ⟨((⟨a, hPN ha⟩ : N) : N ⧸ _), rfl⟩

theorem le_commutator_of_oResidual_eq_top (hG : oResidual p G = ⊤) :
    (P : Subgroup G) ≤ commutator G := by
  refine le_commutator_of_forall_isPGroup_quotient P fun K _ hK => ?_
  rw [eq_top_iff, ← hG]
  have := oResidual_le_ker_of_isPGroup (QuotientGroup.mk' K) hK
  rwa [QuotientGroup.ker_mk'] at this

theorem yoshida_inf_commutator_eq
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) :
    (P : Subgroup G) ⊓ commutator G = (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) :=
  inf_commutator_eq_inf_map_commutator_normalizer P hW

theorem yoshida_bijective_abelianPQuotientMap
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) :
    Function.Bijective (abelianPQuotientMap p N) :=
  bijective_abelianPQuotientMap_of_inf_eq P (inf_commutator_eq_inf_map_commutator_normalizer P hW)

@[expose] noncomputable def yoshidaAbelianPQuotientEquiv
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) :
    N ⧸ (commutator N ⊔ oResidual p N) ≃* G ⧸ (commutator G ⊔ oResidual p G) :=
  MulEquiv.ofBijective (abelianPQuotientMap p N) (yoshida_bijective_abelianPQuotientMap P hW)

theorem yoshidaAbelianPQuotientEquiv_apply
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))))
    (x : N) :
    yoshidaAbelianPQuotientEquiv P hW (x : N ⧸ (commutator N ⊔ oResidual p N)) =
      ((x : G) : G ⧸ (commutator G ⊔ oResidual p G)) :=
  rfl

theorem yoshida_eq_commutator_normalizer_of_oResidual_eq_top
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))))
    (hG : oResidual p G = ⊤) :
    (P : Subgroup G) = ⁅(P : Subgroup G), N⁆ := by
  rw [← inf_map_commutator_normalizer_eq_commutator P,
    ← inf_commutator_eq_inf_map_commutator_normalizer P hW,
    inf_eq_left.mpr (le_commutator_of_oResidual_eq_top P hG)]

theorem yoshida_transfer_theorem
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) :
    ((P : Subgroup G) ⊓ commutator G =
        (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) ∧
      (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) = ⁅(P : Subgroup G), N⁆) ∧
    Function.Bijective (abelianPQuotientMap p N) ∧
    (oResidual p G = ⊤ → (P : Subgroup G) = ⁅(P : Subgroup G), N⁆) :=
  ⟨⟨yoshida_inf_commutator_eq P hW, inf_map_commutator_normalizer_eq_commutator P⟩,
    yoshida_bijective_abelianPQuotientMap P hW,
    yoshida_eq_commutator_normalizer_of_oResidual_eq_top P hW⟩

end CFSG.RankThree.Transfer

end

public section

namespace CFSG.RankThree.Transfer

universe u

theorem yoshida_transfer_toolkit_form :
    ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ P : Sylow p G,
      (∀ (N : Subgroup (P : Subgroup G)) [N.Normal],
        IsEmpty ((↥(P : Subgroup G) ⧸ N) ≃*
          (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) →
      ((P : Subgroup G) ⊓ commutator G =
          (P : Subgroup G) ⊓ (commutator (Subgroup.normalizer (P : Set G))).map
            (Subgroup.normalizer (P : Set G)).subtype) ∧
        ((∀ (N : Subgroup G) [N.Normal], IsPGroup p (G ⧸ N) → N = ⊤) →
          (P : Subgroup G) =
            ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆) := by
  intro G _ _ p hp P hW
  have := Fact.mk hp
  have h1 := inf_commutator_eq_inf_map_commutator_normalizer P hW
  refine ⟨h1, fun hG => ?_⟩
  rw [← inf_map_commutator_normalizer_eq_commutator P, ← h1,
    inf_eq_left.mpr (le_commutator_of_forall_isPGroup_quotient P hG)]

end CFSG.RankThree.Transfer

end
