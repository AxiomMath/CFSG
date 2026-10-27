module

public import CFSG.Quasithin.Background.AutOnEquiv
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Vol2.Ch3T325E
public import CFSG.Quasithin.Background.FFC5Two

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

section Restrict

variable {G : Type} [Group G] {L V₀ VM : Subgroup G} [IsMulCommutative ↥VM]
  [IsMulCommutative ↥V₀]

theorem exists_resHom (hV : V₀ ≤ VM) (hLV₀ : L ≤ Subgroup.normalizer (V₀ : Set G))
    (hLVM : L ≤ Subgroup.normalizer (VM : Set G)) :
    ∃ ρ : ↥(autOn L VM) →* ↥(autOn L V₀), Function.Surjective ρ ∧
      ∀ (φ : ↥(autOn L VM)) (v : ↥V₀),
        (((ρ φ : MulAut ↥V₀) v : ↥V₀) : G) = (((φ : MulAut ↥VM) ⟨v, hV v.2⟩ : ↥VM) : G) := by
  have hstab : autOn L VM ≤ stabSub (V₀.subgroupOf VM) := by
    intro φ hφ u
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hφ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, InternalSec.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hLV₀ hgL) u).symm
  set e := Subgroup.subgroupOfEquivOfLe hV with he
  set f : ↥(autOn L VM) →* MulAut ↥V₀ :=
    (congrHom e).comp ((resHom (V₀.subgroupOf VM)).comp (Subgroup.inclusion hstab)) with hf
  have hfv : ∀ (φ : ↥(autOn L VM)) (v : ↥V₀),
      ((f φ v : ↥V₀) : G) = (((φ : MulAut ↥VM) ⟨v, hV v.2⟩ : ↥VM) : G) := fun φ v => rfl
  have hconj : ∀ g : ↥(Subgroup.normalizer (VM : Set G)), ∀ hgL : (g : G) ∈ L,
      ∀ h : (g : G) ∈ Subgroup.normalizer (V₀ : Set G),
        f ⟨conjAct VM g, Setup.mem_autOn_iff.mpr ⟨g, hgL, rfl⟩⟩ = conjAct V₀ ⟨g, h⟩ := by
    intro g hgL h
    ext v
    rw [hfv, InternalSec.coe_conjAct_apply, InternalSec.coe_conjAct_apply]
  have hmem : ∀ φ, f φ ∈ autOn L V₀ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hφ
    rw [hconj g hgL (hLV₀ hgL)]
    exact Setup.mem_autOn_iff.mpr ⟨_, hgL, rfl⟩
  refine ⟨f.codRestrict _ hmem, ?_, fun φ v => hfv φ v⟩
  rintro ⟨ψ, hψ⟩
  obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hψ
  refine ⟨⟨conjAct VM ⟨g, hLVM hgL⟩, Setup.mem_autOn_iff.mpr ⟨_, hgL, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show f _ = _
  rw [hconj ⟨g, hLVM hgL⟩ hgL (hLV₀ hgL)]

theorem realizes_restrict (hV : V₀ ≤ VM) (hLV₀ : L ≤ Subgroup.normalizer (V₀ : Set G))
    (hLVM : L ≤ Subgroup.normalizer (VM : Set G)) {D : FFModel}
    (h : D.Realizes (autOn L VM) (V₀.subgroupOf VM) ⊥) : D.Realizes (autOn L V₀) ⊤ ⊥ := by
  obtain ⟨π, hπs, -, hks, hHU, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  obtain ⟨ρ, hρs, hρ⟩ := exists_resHom hV hLV₀ hLVM
  let ι : ↥(⊤ : Subgroup ↥V₀) →* ↥(V₀.subgroupOf VM) :=
    { toFun := fun v => ⟨⟨v, hV v.1.2⟩, v.1.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : ∀ v : ↥(⊤ : Subgroup ↥V₀), (((ι v : ↥(V₀.subgroupOf VM)) : ↥VM) : G) = v.1 :=
    fun _ => rfl
  refine ⟨ρ.comp π, hρs.comp hπs, bot_le, hks, fun _ _ _ => trivial, fun x z hz => ?_, hsec,
    hker, β.comp ι, ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro q
    obtain ⟨u, rfl⟩ := hβs q
    exact ⟨⟨⟨(u : ↥VM), u.2⟩, trivial⟩, congrArg β (Subtype.ext (Subtype.ext rfl))⟩
  · rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      exact Subtype.ext (by simpa [hι] using congrArg Subtype.val h1)
    · intro h1
      apply Subtype.ext
      show ((u : ↥V₀) : G) = 1
      rw [h1]
      rfl
  · have hu' : ((π γ : ↥(autOn L VM)) : MulAut ↥VM) ((ι u : ↥(V₀.subgroupOf VM)) : ↥VM) ∈
        V₀.subgroupOf VM := hHU (π γ) _ (ι u).2
    have h1 := hβe γ (ι u) m hu' hm hum
    rw [MonoidHom.comp_apply]
    convert h1 using 2
    apply Subtype.ext
    apply Subtype.ext
    exact hρ (π γ) u

end Restrict

section Faithful

theorem injective_of_faithful' {V : Type*} [CommGroup V] {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

variable {G : Type} [Group G] {L V₀ VM : Subgroup G}

theorem inf_centralizer_le_of_faithful [IsMulCommutative ↥VM] {D : FFModel} (hD : D.Faithful)
    (hLVM : L ≤ Subgroup.normalizer (VM : Set G)) {Z : Subgroup ↥VM}
    (h : D.Realizes (autOn L VM) (V₀.subgroupOf VM) Z) :
    L ⊓ Subgroup.centralizer (V₀ : Set G) ≤ Subgroup.centralizer (VM : Set G) := by
  obtain ⟨π, hπ⟩ := h
  rintro l ⟨hlL, hlC⟩
  have hx := FFC.faithful_on_of_realizes hD hπ (conjAct VM ⟨l, hLVM hlL⟩)
    (Setup.mem_autOn_iff.mpr ⟨_, hlL, rfl⟩) fun u hu => by
      apply Subtype.ext
      rw [InternalSec.coe_conjAct_apply]
      have hc := Subgroup.mem_centralizer_iff.mp hlC (u : G) (Subgroup.mem_subgroupOf.mp hu)
      rw [← hc, mul_inv_cancel_right]
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have h1 := congrArg (fun φ : MulAut ↥VM => ((φ ⟨v, hv⟩ : ↥VM) : G)) hx
  simp only [InternalSec.coe_conjAct_apply, MulAut.one_apply] at h1
  calc v * l = (l * v * l⁻¹) * l := by rw [h1]
    _ = l * v := by group

theorem nonempty_autOn_equiv {V W : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (h : L ⊓ Subgroup.centralizer (V : Set G) = L ⊓ Subgroup.centralizer (W : Set G)) :
    Nonempty (↥(autOn L V) ≃* ↥(autOn L W)) :=
  CFSG.Quasithin.InternalSec.nonempty_autOn_equiv hLV hLW h

end Faithful

end CFSG.Quasithin.H13.T325
