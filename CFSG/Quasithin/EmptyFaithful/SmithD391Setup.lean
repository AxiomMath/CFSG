module

public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.F918N2
public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

theorem iso_of_iso_map {A₁ A₂ : Type*} [Group A₁] [Group A₂] {Q₁ Q₂ : Type*} [CommGroup Q₁]
    [CommGroup Q₂] [MulDistribMulAction A₁ Q₁] [MulDistribMulAction A₂ Q₂] (ι : Q₁ →* Q₂)
    (hι : Function.Injective ι) (f : A₁ → A₂) (hf : ∀ (a : A₁) (x : Q₁), ι (a • x) = f a • ι x)
    {S S' : Subgroup Q₁} (h : XMod.Iso A₂ (S.map ι) (S'.map ι)) : XMod.Iso A₁ S S' := by
  obtain ⟨φ, hφ⟩ := h
  let e : ↥S ≃* ↥S' := ((Subgroup.equivMapOfInjective S ι hι).trans φ).trans
    (Subgroup.equivMapOfInjective S' ι hι).symm
  have he : ∀ l : ↥S, ι ((e l : ↥S') : Q₁) =
      ((φ (Subgroup.equivMapOfInjective S ι hι l) : ↥(S'.map ι)) : Q₂) := by
    intro l
    have : (Subgroup.equivMapOfInjective S' ι hι) (e l) =
        φ (Subgroup.equivMapOfInjective S ι hι l) := by
      simp [e]
    rw [← this]
    rfl
  refine ⟨e, fun a l l' hl => hι ?_⟩
  rw [hf, he, he]
  refine hφ (f a) _ _ ?_
  show f a • ι (l : Q₁) = ι (l' : Q₁)
  rw [← hf, hl]

section Iota

variable {W : Type} [CommGroup W]

theorem modFix_top_eq (L : Subgroup (MulAut W)) : modFix L (⊤ : Subgroup W) = fixV L :=
  (fixed_eq_inf_fixV L ⊤).trans (top_inf_eq _)

@[expose] noncomputable def iotaQ (L : Subgroup (MulAut W)) (VT : Subgroup W) :
    Sec VT (VT ⊓ fixV L) →* W ⧸ modFix L (⊤ : Subgroup W) :=
  QuotientGroup.map ((VT ⊓ fixV L).subgroupOf VT) (modFix L ⊤) VT.subtype
    (fun x hx => by
      rw [Subgroup.mem_comap, modFix_top_eq]
      exact hx.2)

theorem iotaQ_mk (L : Subgroup (MulAut W)) (VT : Subgroup W) (x : ↥VT) :
    iotaQ L VT (QuotientGroup.mk x) = QuotientGroup.mk (x : W) := rfl

theorem iotaQ_injective (L : Subgroup (MulAut W)) (VT : Subgroup W) :
    Function.Injective (iotaQ L VT) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [iotaQ_mk, QuotientGroup.eq_one_iff, modFix_top_eq] at hy
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨x.2, hy⟩

theorem map_iotaQ_sec35Img (L : Subgroup (MulAut W)) {VT I : Subgroup W} (hI : I ≤ VT) :
    (sec35Img VT (VT ⊓ fixV L) I).map (iotaQ L VT) = tilde L ⊤ I := by
  ext q
  unfold sec35Img
  rw [Subgroup.map_map, mem_tilde_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hI hv⟩, hv, rfl⟩

variable {M L : Subgroup (MulAut W)} (hML : M ≤ Subgroup.normalizer (L : Set (MulAut W)))

theorem iotaQ_rho {VT : Subgroup W}
    (g : ↥(stabSub VT ⊓ stabSub (VT ⊓ fixV L))) (hgM : (g : MulAut W) ∈ M)
    (x : Sec VT (VT ⊓ fixV L)) :
    letI := quotAct (W := (⊤ : Subgroup W)) hML (fun _ _ _ _ => trivial)
    iotaQ L VT (n2Rho VT (VT ⊓ fixV L) g x) = (⟨g, hgM⟩ : ↥M) • iotaQ L VT x := by
  induction x using QuotientGroup.induction_on with
  | H w => rfl

end Iota

section Situation

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem d391_lt (hdeep : V = commSub V L ∧ commSub V L < commSub (orbSup T V) L) :
    V < orbSup T V := by
  refine lt_of_le_of_ne (le_orbSup T V) fun h => ?_
  apply hdeep.2.ne
  rw [← h]

theorem d391_cent (hD : D3Std M L T L V) :
    ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g := by
  intro g hg hgV x hx
  have hq : CFSG.IsQuasisimple ↥L := hD.hyp.quasi
  obtain ⟨hLV, -, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  set K : Subgroup ↥L :=
    { carrier := {k | ∀ v ∈ V, (k : MulAut W) v = v}
      one_mem' := fun v _ => rfl
      mul_mem' := fun {a b} ha hb v hv => by
        show (a : MulAut W) ((b : MulAut W) v) = v
        rw [hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv => by
        show (a : MulAut W)⁻¹ v = v
        nth_rewrite 1 [← ha v hv]
        exact MulAut.inv_apply_self _ _ _ } with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk l v hv => ?_⟩
    show ((l : MulAut W) * (k : MulAut W) * (l : MulAut W)⁻¹) v = v
    have h1 : (l : MulAut W)⁻¹ v ∈ V := hLV _ (L.inv_mem l.2) v hv
    simp only [MulAut.mul_apply]
    rw [hk _ h1, MulAut.apply_inv_self]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKn with h | h
  · exfalso
    apply hVlt.ne
    refine le_antisymm inf_le_left fun v hv => ⟨hv, mem_fixV.2 fun a ha => ?_⟩
    have hmem : (⟨a, ha⟩ : ↥L) ∈ K := by rw [h]; trivial
    exact hmem v hv
  · have hgK : (⟨g, hg⟩ : ↥L) ∈ K := hgV
    have := Subgroup.mem_center_iff.mp (h hgK) ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm

end Situation

end CFSG.Quasithin.SmithD391
