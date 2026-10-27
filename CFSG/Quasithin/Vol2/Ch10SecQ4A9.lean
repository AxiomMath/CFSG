module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G Y : Type} [Group G] [Group Y] {L : Subgroup G} (f : ↥L →* Y)

theorem imgL_sup {A B : Subgroup G} (hA : A ≤ L) (hB : B ≤ L) :
    imgL f (A ⊔ B) = imgL f A ⊔ imgL f B := by
  rw [imgL, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

theorem imgL_bot : imgL f (⊥ : Subgroup G) = ⊥ := by
  rw [imgL, Subgroup.bot_subgroupOf, Subgroup.map_bot]

variable (hkQ : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockQ L)
  (hkU : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockU L → (x : G) = 1)
include hkQ hkU

theorem blockZ_range_eq_bot [Finite G] (hZ : blockZ L = ⊥) : blockZ f.range = ⊥ := by
  rw [blockZ_range f hkQ hkU, hZ, imgL_bot]

theorem isAltType_range [Finite G] (hL : IsShort2 L) (h5 : IsAltType L 5) :
    IsAltType f.range 5 := by
  obtain ⟨α, hα, hαk, β, hβs, hβk, hβe⟩ := h5
  have hUL : blockU L ≤ L := hL.2.2.1.1.trans (inf_le_left.trans
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  have hU := blockU_range f hkQ
  have hZ := blockZ_range f hkQ hkU
  have hker : f.rangeRestrict.ker ≤ α.ker := by
    intro x hx
    rw [hαk]
    refine mem_pCore_of_mem_blockQ (hkQ x ?_)
    have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
    simpa using this
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective f.rangeRestrict
    f.rangeRestrict_surjective
  let α' : ↥f.range →* ↥(alternatingGroup (Fin 5)) :=
    (QuotientGroup.lift _ α hker).comp e₁.symm.toMonoidHom
  have hα' : ∀ x, α' (f.rangeRestrict x) = α x := by
    intro x
    have : e₁.symm (f.rangeRestrict x) = QuotientGroup.mk x :=
      e₁.symm_apply_eq.mpr rfl
    simp only [α', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this,
      QuotientGroup.lift_mk]
  let ε₀ : ↥(blockU L) →* ↥(blockU f.range) :=
    { toFun := fun u => ⟨f ⟨u, hUL u.2⟩, hU ▸ (mem_imgL f).mpr ⟨_, u.2, rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun u v => Subtype.ext (by
        show f ⟨u * v, _⟩ = f ⟨u, _⟩ * f ⟨v, _⟩
        rw [← map_mul]
        rfl) }
  have hε₀ : Function.Bijective ε₀ := by
    refine ⟨fun u v huv => ?_, fun y => ?_⟩
    · have := eq_of_mem_blockU f hkU u.2 v.2 (congrArg Subtype.val huv)
      exact Subtype.ext (Subtype.mk.inj this)
    · have hy : (y : Y) ∈ imgL f (blockU L) := hU.le y.2
      obtain ⟨x, hxU, hx⟩ := (mem_imgL f).mp hy
      exact ⟨⟨x, hxU⟩, Subtype.ext hx⟩
  let ε := MulEquiv.ofBijective ε₀ hε₀
  have hε : ∀ u : ↥(blockU L), ((ε u : ↥(blockU f.range)) : Y) = f ⟨u, hUL u.2⟩ :=
    fun u => rfl
  refine ⟨α', ?_, ?_, β.comp ε.symm.toMonoidHom, hβs.comp ε.symm.surjective, ?_, ?_⟩
  · intro σ
    obtain ⟨x, rfl⟩ := hα σ
    exact ⟨_, hα' x⟩
  · ext y
    obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective y
    rw [MonoidHom.mem_ker, hα', ← MonoidHom.mem_ker, hαk]
    exact (mem_pCore_range_iff f hkQ x).symm
  · ext y
    obtain ⟨u, rfl⟩ := ε.surjective y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, hε, hZ, mem_imgL]
    constructor
    · intro hu
      exact ⟨⟨u, hUL u.2⟩, hu, rfl⟩
    · rintro ⟨x, hxZ, hx⟩
      have := congrArg Subtype.val (eq_of_mem_blockU f hkU hxZ.1 u.2 hx)
      simp only at this
      rw [← this]
      exact hxZ
  · intro ℓ' u' v' huv i
    obtain ⟨ℓ, rfl⟩ := f.rangeRestrict_surjective ℓ'
    obtain ⟨u, rfl⟩ := ε.surjective u'
    obtain ⟨v, rfl⟩ := ε.surjective v'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [hα']
    have hUn : L ≤ Subgroup.normalizer (blockU L : Set G) := le_normalizer_blockU L
    have hconj : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hUn ℓ.2) _).mp u.2
    have h1 : f ⟨v, hUL v.2⟩ = f (ℓ * ⟨u, hUL u.2⟩ * ℓ⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← hε, ← hε, huv]
      rfl
    have h2 := eq_of_mem_blockU f hkU v.2 hconj h1
    exact hβe ℓ u v (congrArg Subtype.val h2) i

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
