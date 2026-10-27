module

public import CFSG.Quasithin.EmptyFaithful.SBc9Fix
public import CFSG.Quasithin.EmptyFaithful.SBc9HeartDual
public import CFSG.Quasithin.EmptyFaithful.SBc7Hyp
public import CFSG.Quasithin.EmptyFaithful.SBc8V2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc9

section Dict

variable {G : Type} [Group G] {L : Subgroup G}

theorem heartAct_toAdd_beta {α : ↥L →* alternatingGroup (Fin 6)}
    {β : ↥(blockU L) →* Multiplicative (AltHeart 6)}
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (α ℓ : Equiv.Perm (Fin 6)) x) : AltHeart 6) =
          Multiplicative.toAdd (β v))
    (ℓ : ↥L) (u v : ↥(blockU L)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    heartAct (α ℓ : Equiv.Perm (Fin 6)) (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β v) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
  rw [← hx]
  exact hβe ℓ u v h x hx

end Dict

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem alt6_noFixed (h113 : StageLemma14113) (c : Ctx15330 T Mc M V₁ V₂ Yp I L t)
    {α : ↥L →* ↥(alternatingGroup (Fin 6))} (hα : IsAltBlockTypeWith L 6 α) :
    ∀ u : AltHeart 6, (∀ y ∈ (Yp.subgroupOf L).map α,
      heartAct (y : Equiv.Perm (Fin 6)) u = u) → u = 0 := by
  obtain ⟨hαs, -, β, -, hβk, hβe⟩ := hα
  obtain ⟨-, hV₂Q, hMN, hV₂card, hV₂fix⟩ := SBc8.V₂_facts h113 c
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hSM : Sgp153 T V₁ ≤ M ⊓ I := le_inf (inf_le_right.trans c.c29.norm_le) hsyl.1
  have hYM : Yp ≤ M ⊓ I := by
    rw [hF.yp_eq]
    exact SBc5.oPrimeResidualOf_le 3 _
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := SBc7.Sgp_le_normalizer_Yp c
  let Ybar : Subgroup ↥(alternatingGroup (Fin 6)) := (Yp.subgroupOf L).map α
  let Tbar : Subgroup ↥(alternatingGroup (Fin 6)) := ((Sgp153 T V₁ ⊓ L).subgroupOf L).map α
  have hTbar : IsSylowTwoOf Tbar ⊤ :=
    SBc5.isSylowTwoOf_map_surjective α hαs (SBc5.isSylowTwoOf_subgroupOf_top hQsyl)
  have hN : ∀ τ ∈ Tbar, ∀ y ∈ Ybar, τ * y * τ⁻¹ ∈ Ybar := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨s * y * s⁻¹, ?_, by simp⟩
    show (s : G) * (y : G) * (s : G)⁻¹ ∈ Yp
    exact (Subgroup.mem_normalizer_iff.mp (hSN hs.1) (y : G)).mp hy
  have hconj : ∀ (s : ↥L) (v : G) (hv : v ∈ V₂) (hsv : (s : G) * v * (s : G)⁻¹ ∈ V₂),
      heartAct (α s : Equiv.Perm (Fin 6)) (Multiplicative.toAdd (β ⟨v, hV₂Q hv⟩)) =
        Multiplicative.toAdd (β ⟨(s : G) * v * (s : G)⁻¹, hV₂Q hsv⟩) :=
    fun s v hv hsv => heartAct_toAdd_beta hβe s _ _ rfl
  let E : AddSubgroup (AltHeart 6) :=
    { carrier := {x | ∃ v : G, ∃ hv : v ∈ V₂, Multiplicative.toAdd (β ⟨v, hV₂Q hv⟩) = x}
      zero_mem' := ⟨1, V₂.one_mem, by
        rw [show (⟨1, hV₂Q V₂.one_mem⟩ : ↥(blockU L)) = 1 from rfl, map_one]
        rfl⟩
      add_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
        refine ⟨v * v', V₂.mul_mem hv hv', ?_⟩
        rw [show (⟨v * v', hV₂Q (V₂.mul_mem hv hv')⟩ : ↥(blockU L)) =
          ⟨v, hV₂Q hv⟩ * ⟨v', hV₂Q hv'⟩ from rfl, map_mul, toAdd_mul]
      neg_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨v⁻¹, V₂.inv_mem hv, ?_⟩
        rw [show (⟨v⁻¹, hV₂Q (V₂.inv_mem hv)⟩ : ↥(blockU L)) =
          (⟨v, hV₂Q hv⟩ : ↥(blockU L))⁻¹ from rfl, map_inv, toAdd_inv] }
  have hE : E ≠ ⊥ := by
    intro hbot
    have hV₂ne : V₂ ≠ ⊥ := by
      intro h
      rw [h] at hV₂card
      simp at hV₂card
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₂ne
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hmem : Multiplicative.toAdd (β ⟨v, hV₂Q hv⟩) ∈ E := ⟨v, hv, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    have h1 : β ⟨v, hV₂Q hv⟩ = 1 := Multiplicative.toAdd.injective hmem
    have h2 : (⟨v, hV₂Q hv⟩ : ↥(blockU L)) ∈ β.ker := h1
    rw [hβk] at h2
    have hvZ : v ∈ blockZ L := Subgroup.mem_subgroupOf.mp h2
    obtain ⟨y, hy, hne⟩ := hV₂fix v hv hv1'
    apply hne
    have h := Subgroup.mem_centralizer_iff.mp hvZ.2 y (hYL hy)
    calc y * v * y⁻¹ = (v * y) * y⁻¹ := by rw [h]
      _ = v := by group
  have hET : ∀ τ ∈ Tbar, ∀ e ∈ E, heartAct (τ : Equiv.Perm (Fin 6)) e ∈ E := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨v, hv, rfl⟩
    have hsS : (s : G) ∈ Sgp153 T V₁ := hs.1
    have hsv : (s : G) * v * (s : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hMN (hSM hsS)) v).mp hv
    rw [hconj s v hv hsv]
    exact ⟨_, hsv, rfl⟩
  have hCE : ∀ e ∈ E, (∀ y ∈ Ybar, heartAct (y : Equiv.Perm (Fin 6)) e = e) → e = 0 := by
    rintro _ ⟨v, hv, rfl⟩ hfix
    by_contra hne
    have hv1 : v ≠ 1 := by
      rintro rfl
      apply hne
      rw [show (⟨1, hV₂Q V₂.one_mem⟩ : ↥(blockU L)) = 1 from rfl, map_one]
      rfl
    obtain ⟨y, hy, hyne⟩ := hV₂fix v hv hv1
    have hyL : y ∈ L := hYL hy
    have hyv : y * v * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hMN (hYM hy)) v).mp hv
    have h1 := hfix (α ⟨y, hyL⟩) ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hconj ⟨y, hyL⟩ v hv hyv] at h1
    have h2 : β ⟨y * v * y⁻¹, hV₂Q hyv⟩ = β ⟨v, hV₂Q hv⟩ := Multiplicative.toAdd.injective h1
    have h3 : (⟨y * v * y⁻¹, hV₂Q hyv⟩ : ↥(blockU L)) * (⟨v, hV₂Q hv⟩ : ↥(blockU L))⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
    rw [hβk] at h3
    have hw : y * v * y⁻¹ * v⁻¹ ∈ blockZ L := Subgroup.mem_subgroupOf.mp h3
    have hwV : y * v * y⁻¹ * v⁻¹ ∈ V₂ := V₂.mul_mem hyv (V₂.inv_mem hv)
    have hw1 : y * v * y⁻¹ * v⁻¹ = 1 := by
      by_contra hw1
      obtain ⟨y', hy', hne'⟩ := hV₂fix _ hwV hw1
      apply hne'
      have h := Subgroup.mem_centralizer_iff.mp hw.2 y' (hYL hy')
      calc y' * (y * v * y⁻¹ * v⁻¹) * y'⁻¹ = ((y * v * y⁻¹ * v⁻¹) * y') * y'⁻¹ := by rw [h]
        _ = y * v * y⁻¹ * v⁻¹ := by group
    exact hyne (by
      calc y * v * y⁻¹ = (y * v * y⁻¹ * v⁻¹) * v := by group
        _ = v := by rw [hw1, one_mul])
  exact heart_noFixed_of_invariant hTbar hN E hE hET hCE

theorem alt6_centralizer_le_blockZ (h113 : StageLemma14113) (c : Ctx15330 T Mc M V₁ V₂ Yp I L t)
    (hAlt : IsAltBlockType L 6) :
    ∀ q ∈ blockU L, q ∈ Subgroup.centralizer (Yp : Set G) → q ∈ blockZ L := by
  intro q hq hqC
  obtain ⟨-, α, hα⟩ := hAlt
  have hno := alt6_noFixed h113 c hα
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hα
  have hu : Multiplicative.toAdd (β ⟨q, hq⟩) = 0 := by
    apply hno
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hy
    have hyq : (y : G) * q * (y : G)⁻¹ = q := by
      have h := Subgroup.mem_centralizer_iff.mp hqC y hy'
      calc (y : G) * q * (y : G)⁻¹ = (q * (y : G)) * (y : G)⁻¹ := by rw [h]
        _ = q := by group
    exact heartAct_toAdd_beta hβe y ⟨q, hq⟩ ⟨q, hq⟩ hyq.symm
  have h1 : β ⟨q, hq⟩ = 1 := Multiplicative.toAdd.injective hu
  have h2 : (⟨q, hq⟩ : ↥(blockU L)) ∈ β.ker := h1
  rw [hβk] at h2
  exact Subgroup.mem_subgroupOf.mp h2

theorem alt6_blockU_cover (h113 : StageLemma14113) (c : Ctx15330 T Mc M V₁ V₂ Yp I L t)
    (hAlt : IsAltBlockType L 6) :
    ∀ q ∈ blockU L, ∃ r ∈ ⁅blockU L, Yp⁆, r⁻¹ * q ∈ blockZ L := by
  obtain ⟨-, α, hα⟩ := hAlt
  have hno := alt6_noFixed h113 c hα
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := hα
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hLQ : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 L) L
  let H : AddSubgroup (AltHeart 6) :=
    { carrier := {x | ∃ r : G, ∃ hr : r ∈ blockU L, r ∈ ⁅blockU L, Yp⁆ ∧
        Multiplicative.toAdd (β ⟨r, hr⟩) = x}
      zero_mem' := ⟨1, (blockU L).one_mem, (⁅blockU L, Yp⁆).one_mem, by
        rw [show (⟨1, (blockU L).one_mem⟩ : ↥(blockU L)) = 1 from rfl, map_one]
        rfl⟩
      add_mem' := by
        rintro _ _ ⟨r, hr, hrR, rfl⟩ ⟨r', hr', hr'R, rfl⟩
        refine ⟨r * r', (blockU L).mul_mem hr hr', (⁅blockU L, Yp⁆).mul_mem hrR hr'R, ?_⟩
        rw [show (⟨r * r', (blockU L).mul_mem hr hr'⟩ : ↥(blockU L)) = ⟨r, hr⟩ * ⟨r', hr'⟩ from rfl,
          map_mul, toAdd_mul]
      neg_mem' := by
        rintro _ ⟨r, hr, hrR, rfl⟩
        refine ⟨r⁻¹, (blockU L).inv_mem hr, (⁅blockU L, Yp⁆).inv_mem hrR, ?_⟩
        rw [show (⟨r⁻¹, (blockU L).inv_mem hr⟩ : ↥(blockU L)) = (⟨r, hr⟩ : ↥(blockU L))⁻¹ from rfl,
          map_inv, toAdd_inv] }
  have hH : ∀ y ∈ (Yp.subgroupOf L).map α, ∀ u : AltHeart 6,
      heartAct (y : Equiv.Perm (Fin 6)) u - u ∈ H := by
    rintro _ ⟨y, hy, rfl⟩ u
    have hy' : (y : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd u)
    have hu : u = Multiplicative.toAdd (β q) := by rw [hq]; rfl
    have hyq : (y : G) * q * (y : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hLQ y.2) q).mp q.2
    have hcomm : (y : G) * q * (y : G)⁻¹ * (q : G)⁻¹ ∈ ⁅blockU L, Yp⁆ := by
      have h := Subgroup.commutator_mem_commutator hy' q.2
      rw [Subgroup.commutator_comm] at h
      rw [commutatorElement_def] at h
      exact h
    refine ⟨_, (blockU L).mul_mem hyq ((blockU L).inv_mem q.2), hcomm, ?_⟩
    have hdecomp : (⟨(y : G) * q * (y : G)⁻¹ * (q : G)⁻¹,
        (blockU L).mul_mem hyq ((blockU L).inv_mem q.2)⟩ : ↥(blockU L)) =
        ⟨(y : G) * q * (y : G)⁻¹, hyq⟩ * q⁻¹ := rfl
    rw [hdecomp, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    have h1 := heartAct_toAdd_beta hβe y q ⟨(y : G) * q * (y : G)⁻¹, hyq⟩ rfl
    rw [← h1, ← hu]
  have htop := heart_eq_top_of_commutators hno H hH
  intro q hq
  have hmem : Multiplicative.toAdd (β ⟨q, hq⟩) ∈ H := by rw [htop]; trivial
  obtain ⟨r, hr, hrR, hrq⟩ := hmem
  refine ⟨r, hrR, ?_⟩
  have h1 : β ⟨r, hr⟩ = β ⟨q, hq⟩ := Multiplicative.toAdd.injective hrq
  have h2 : (⟨r, hr⟩ : ↥(blockU L))⁻¹ * ⟨q, hq⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [hβk] at h2
  exact Subgroup.mem_subgroupOf.mp h2

end Main

end SBc9

end CFSG.Quasithin
