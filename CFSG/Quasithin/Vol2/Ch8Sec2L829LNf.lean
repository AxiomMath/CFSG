module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNc
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN3
public import CFSG.Quasithin.Background.Ordering
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

private abbrev toWf_LNf {W : Type} (a : Multiplicative W) : W := Additive.ofMul a

private lemma comm_of_comm_one_LNf {M : Type} [Group M] {a b : M}
    (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

private lemma conj_comm_gen_LNf {M : Type} [Group M] (a b c : M) (hc : b * c = c * b) :
    a * b * a⁻¹ * (a * c * a⁻¹) = a * c * a⁻¹ * (a * b * a⁻¹) := by
  calc a * b * a⁻¹ * (a * c * a⁻¹) = a * (b * c) * a⁻¹ := by group
    _ = a * (c * b) * a⁻¹ := by rw [hc]
    _ = a * c * a⁻¹ * (a * b * a⁻¹) := by group

private lemma rho_comm_VLu_LNf {G : Type} [Group G] {Λ W₀ W₁ Lu V : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (SW : SectionModule Λ W₀ W₁ W) (hLuΛ : Lu ≤ Λ)
    (hVLu : ⁅V, Lu⁆ ≤ pCoreOf 2 Lu)
    (hQ : ∀ q ∈ pCoreOf 2 Lu, ∀ x ∈ W₁, q * x * q⁻¹ * x⁻¹ ∈ W₀)
    {v : G} (hv : v ∈ V) (hvΛ : v ∈ Λ) (z : ↥Λ) (hz : (z : G) ∈ Lu) :
    SW.ρ ⟨v, hvΛ⟩ * SW.ρ z = SW.ρ z * SW.ρ ⟨v, hvΛ⟩ := by
  have hc : v * (z : G) * v⁻¹ * (z : G)⁻¹ ∈ pCoreOf 2 Lu :=
    hVLu (Subgroup.commutator_mem_commutator hv hz)
  have hcΛ : v * (z : G) * v⁻¹ * (z : G)⁻¹ ∈ Λ :=
    hLuΛ (CFSG.LieType.BorelTits.pCoreOf_le 2 Lu hc)
  have h1 : SW.ρ ((⟨v, hvΛ⟩ : ↥Λ) * z * (⟨v, hvΛ⟩ : ↥Λ)⁻¹ * z⁻¹) = 1 := by
    have e : (⟨v, hvΛ⟩ : ↥Λ) * z * (⟨v, hvΛ⟩ : ↥Λ)⁻¹ * z⁻¹ =
        (⟨v * (z : G) * v⁻¹ * (z : G)⁻¹, hcΛ⟩ : ↥Λ) := Subtype.ext rfl
    rw [e]
    exact SW.ρ_eq_one _ (fun x => hQ _ hc x x.2)
  apply comm_of_comm_one_LNf
  simpa only [map_mul, map_inv] using h1

private lemma img_conj_mem_LNf {G : Type} [Group G] {Λ W₀ W₁ : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (SW : SectionModule Λ W₀ W₁ W) {X : Subgroup G}
    (a : ↥Λ) (haX : ∀ y ∈ X, (a : G) * y * (a : G)⁻¹ ∈ X) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ SW.img X) : SW.ρ a * g * (SW.ρ a)⁻¹ ∈ SW.img X := by
  obtain ⟨y, hyX, rfl⟩ := SW.mem_img.mp hg
  have e : SW.ρ a * SW.ρ y * (SW.ρ a)⁻¹ = SW.ρ (a * y * a⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e]
  exact SW.mem_img.mpr ⟨a * y * a⁻¹, haX y hyX, rfl⟩

private lemma comm_closure_LNf {G : Type} [Group G] {Λ W₀ W₁ Lu H V : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (SW : SectionModule Λ W₀ W₁ W)
    (hLuΛ : Lu ≤ Λ) (hHΛ : H ≤ Λ) (hVH : V ≤ H)
    (hHLu : H ≤ Subgroup.normalizer (Lu : Set G)) (hVLu : ⁅V, Lu⁆ ≤ pCoreOf 2 Lu)
    (hQ : ∀ q ∈ pCoreOf 2 Lu, ∀ x ∈ W₁, q * x * q⁻¹ * x⁻¹ ∈ W₀)
    {y : G} (hy : y ∈ conjClosure V H) :
    ∃ hyΛ : y ∈ Λ, ∀ z : ↥Λ, (z : G) ∈ Lu →
      SW.ρ ⟨y, hyΛ⟩ * SW.ρ z = SW.ρ z * SW.ρ ⟨y, hyΛ⟩ := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, v, hv, rfl⟩ := hx
    have hvΛ : v ∈ Λ := hHΛ (hVH hv)
    have hhΛ : h ∈ Λ := hHΛ hh
    have hyΛ : h * v * h⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hhΛ hvΛ) (Λ.inv_mem hhΛ)
    refine ⟨hyΛ, fun z hz => ?_⟩
    obtain ⟨Z, rfl⟩ : ∃ Z : ↥Λ, z = (⟨h, hhΛ⟩ : ↥Λ) * Z * (⟨h, hhΛ⟩ : ↥Λ)⁻¹ :=
      ⟨(⟨h, hhΛ⟩ : ↥Λ)⁻¹ * z * (⟨h, hhΛ⟩ : ↥Λ), by group⟩
    have hZLu : (Z : G) ∈ Lu := (Subgroup.mem_normalizer_iff.mp (hHLu hh) (Z : G)).mpr hz
    have e1 : (⟨h * v * h⁻¹, hyΛ⟩ : ↥Λ) =
        (⟨h, hhΛ⟩ : ↥Λ) * (⟨v, hvΛ⟩ : ↥Λ) * (⟨h, hhΛ⟩ : ↥Λ)⁻¹ := Subtype.ext rfl
    rw [e1]
    simp only [map_mul, map_inv]
    exact conj_comm_gen_LNf _ _ _ (rho_comm_VLu_LNf SW hLuΛ hVLu hQ hv hvΛ Z hZLu)
  | one =>
    refine ⟨Λ.one_mem, fun z _ => ?_⟩
    show SW.ρ 1 * SW.ρ z = SW.ρ z * SW.ρ 1
    rw [map_one, one_mul, mul_one]
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxΛ, hcx⟩ := ihx
    obtain ⟨hyΛ, hcy⟩ := ihy
    refine ⟨Λ.mul_mem hxΛ hyΛ, fun z hz => ?_⟩
    have e : (⟨x * y, Λ.mul_mem hxΛ hyΛ⟩ : ↥Λ) = (⟨x, hxΛ⟩ : ↥Λ) * (⟨y, hyΛ⟩ : ↥Λ) :=
      Subtype.ext rfl
    rw [e, map_mul]
    have h1 := hcx z hz
    have h2 := hcy z hz
    calc SW.ρ ⟨x, hxΛ⟩ * SW.ρ ⟨y, hyΛ⟩ * SW.ρ z
        = SW.ρ ⟨x, hxΛ⟩ * (SW.ρ ⟨y, hyΛ⟩ * SW.ρ z) := mul_assoc _ _ _
      _ = SW.ρ ⟨x, hxΛ⟩ * (SW.ρ z * SW.ρ ⟨y, hyΛ⟩) := by rw [h2]
      _ = (SW.ρ ⟨x, hxΛ⟩ * SW.ρ z) * SW.ρ ⟨y, hyΛ⟩ := (mul_assoc _ _ _).symm
      _ = (SW.ρ z * SW.ρ ⟨x, hxΛ⟩) * SW.ρ ⟨y, hyΛ⟩ := by rw [h1]
      _ = SW.ρ z * (SW.ρ ⟨x, hxΛ⟩ * SW.ρ ⟨y, hyΛ⟩) := mul_assoc _ _ _
  | inv x _ ihx =>
    obtain ⟨hxΛ, hcx⟩ := ihx
    refine ⟨Λ.inv_mem hxΛ, fun z hz => ?_⟩
    have e : (⟨x⁻¹, Λ.inv_mem hxΛ⟩ : ↥Λ) = (⟨x, hxΛ⟩ : ↥Λ)⁻¹ := Subtype.ext rfl
    rw [e, map_inv]
    have h1 := hcx z hz
    calc (SW.ρ ⟨x, hxΛ⟩)⁻¹ * SW.ρ z
        = (SW.ρ ⟨x, hxΛ⟩)⁻¹ * (SW.ρ z * SW.ρ ⟨x, hxΛ⟩) * (SW.ρ ⟨x, hxΛ⟩)⁻¹ := by group
      _ = (SW.ρ ⟨x, hxΛ⟩)⁻¹ * (SW.ρ ⟨x, hxΛ⟩ * SW.ρ z) * (SW.ρ ⟨x, hxΛ⟩)⁻¹ := by rw [h1]
      _ = SW.ρ z * (SW.ρ ⟨x, hxΛ⟩)⁻¹ := by group

private lemma gen_le_closure_LNf {G : Type} [Group G] {Λ W₀ W₁ H V T : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (SW : SectionModule Λ W₀ W₁ W)
    (hHΛ : H ≤ Λ) (hVH : V ≤ H)
    (hHsup : SW.img H ≤ SW.img (conjClosure V H) ⊔ SW.img T) :
    ∀ x ∈ conjClosure V H, ∃ hx : x ∈ Λ, SW.ρ ⟨x, hx⟩ ∈ Subgroup.closure
      {g | ∃ v ∈ SW.img V, ∃ u ∈ SW.img (conjClosure V H) ⊔ SW.img T, g = u * v * u⁻¹} := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, v, hv, rfl⟩ := hx
    have hvΛ : v ∈ Λ := hHΛ (hVH hv)
    have hhΛ : h ∈ Λ := hHΛ hh
    have hyΛ : h * v * h⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hhΛ hvΛ) (Λ.inv_mem hhΛ)
    refine ⟨hyΛ, ?_⟩
    have e1 : (⟨h * v * h⁻¹, hyΛ⟩ : ↥Λ) =
        (⟨h, hhΛ⟩ : ↥Λ) * (⟨v, hvΛ⟩ : ↥Λ) * (⟨h, hhΛ⟩ : ↥Λ)⁻¹ := Subtype.ext rfl
    have hu : SW.ρ ⟨h, hhΛ⟩ ∈ SW.img (conjClosure V H) ⊔ SW.img T :=
      hHsup (SW.mem_img.mpr ⟨⟨h, hhΛ⟩, hh, rfl⟩)
    have hv' : SW.ρ ⟨v, hvΛ⟩ ∈ SW.img V := SW.mem_img.mpr ⟨⟨v, hvΛ⟩, hv, rfl⟩
    rw [e1]
    simp only [map_mul, map_inv]
    exact Subgroup.subset_closure ⟨SW.ρ ⟨v, hvΛ⟩, hv', SW.ρ ⟨h, hhΛ⟩, hu, rfl⟩
  | one =>
    refine ⟨Λ.one_mem, ?_⟩
    show SW.ρ 1 ∈ _
    rw [map_one]
    exact Subgroup.one_mem _
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxΛ, hx'⟩ := ihx
    obtain ⟨hyΛ, hy'⟩ := ihy
    refine ⟨Λ.mul_mem hxΛ hyΛ, ?_⟩
    have e : (⟨x * y, Λ.mul_mem hxΛ hyΛ⟩ : ↥Λ) = (⟨x, hxΛ⟩ : ↥Λ) * (⟨y, hyΛ⟩ : ↥Λ) :=
      Subtype.ext rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ hx' hy'
  | inv x _ ih =>
    obtain ⟨hxΛ, hx'⟩ := ih
    refine ⟨Λ.inv_mem hxΛ, ?_⟩
    have e : (⟨x⁻¹, Λ.inv_mem hxΛ⟩ : ↥Λ) = (⟨x, hxΛ⟩ : ↥Λ)⁻¹ := Subtype.ext rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ hx'

theorem config_of_data {G : Type} [Group G] [Finite G] {Λ Lu H T V W₀ W₁ : Subgroup G}
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (SW : SectionModule Λ W₀ W₁ W) (hnt : Nontrivial W)
    (hirr : ∀ P : Submodule (ZMod 2) W, (∀ y : ↥Λ, ∀ w ∈ P, SW.ρ y w ∈ P) → P = ⊥ ∨ P = ⊤)
    (hLuΛ : Lu ≤ Λ) (hHΛ : H ≤ Λ) (hΛ : Λ ≤ Lu ⊔ H) (hTH : T ≤ H)
    (hHLu : H ≤ Subgroup.normalizer (Lu : Set G))
    (hHG : H ≤ conjClosure V H ⊔ T) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVsq : ∀ v ∈ V, v * v = 1)
    (hVLu : ⁅V, Lu⁆ ≤ pCoreOf 2 Lu)
    (hQ : ∀ q ∈ pCoreOf 2 Lu, ∀ x ∈ W₁, q * x * q⁻¹ * x⁻¹ ∈ W₀)
    (hW₁V : W₁ ≤ Subgroup.normalizer (V : Set G))
    (hVne : ∃ v ∈ V, ¬ ∀ x ∈ W₁, v * x * v⁻¹ * x⁻¹ ∈ W₀)
    (hb : HBData (SW.img Lu) (SW.sub (V ⊓ W₁))) :
    TransvConfig (SW.img Lu) (SW.img (conjClosure V H)) (SW.img T) (SW.img V)
      (SW.sub (V ⊓ W₁)) := by
  have hVH : V ≤ H := hVT.trans hTH
  have hTΛ : T ≤ Λ := hTH.trans hHΛ
  have hVΛ : V ≤ Λ := hVH.trans hHΛ
  have hG₀H : conjClosure V H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh)
  have hG₀Λ : conjClosure V H ≤ Λ := hG₀H.trans hHΛ
  have hHsup : SW.img H ≤ SW.img (conjClosure V H) ⊔ SW.img T := by
    have h := SW.img_mono hHG
    rwa [SW.img_sup hG₀Λ hTΛ] at h
  have hsubLH : SW.img (Lu ⊔ H) ≤ SW.img Lu ⊔ SW.img (conjClosure V H) ⊔ SW.img T := by
    rw [SW.img_sup hLuΛ hHΛ, sup_assoc]
    exact sup_le_sup_left hHsup _
  have hTnorm : ∀ t ∈ SW.img T, ∀ g ∈ SW.img (conjClosure V H),
      t * g * t⁻¹ ∈ SW.img (conjClosure V H) := by
    intro t ht g hg
    obtain ⟨a, haT, rfl⟩ := SW.mem_img.mp ht
    exact img_conj_mem_LNf SW a
      (fun y hy => (Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.le_normalizer_conjClosure V H (hTH haT)) y).mp hy) hg
  have hTnormS : ∀ t ∈ SW.img T, ∀ s ∈ SW.img Lu, t * s * t⁻¹ ∈ SW.img Lu := by
    intro t ht s hs
    obtain ⟨a, haT, rfl⟩ := SW.mem_img.mp ht
    exact img_conj_mem_LNf SW a
      (fun y hy => (Subgroup.mem_normalizer_iff.mp (hHLu (hTH haT)) y).mp hy) hs
  have hsupNorm : SW.img (conjClosure V H) ⊔ SW.img T ≤
      Subgroup.normalizer (SW.img (conjClosure V H) : Set (W ≃ₗ[ZMod 2] W)) :=
    sup_le Subgroup.le_normalizer (Subgroup.le_normalizer_iff.mpr hTnorm)
  have hsupNorm' := Subgroup.le_normalizer_iff.mp hsupNorm
  have hVimg : SW.img V ≤ SW.img (conjClosure V H) := SW.img_mono (le_conjClosure V H)
  have hirr' : ∀ P : Submodule (ZMod 2) W,
      InvUnder (SW.img Lu ⊔ SW.img (conjClosure V H) ⊔ SW.img T) P → P = ⊥ ∨ P = ⊤ := by
    intro P hP
    exact hirr P (fun y w hw => hP (SW.ρ y)
      (hsubLH (SW.mem_img.mpr ⟨y, hΛ y.2, rfl⟩)) w hw)
  have hcomm : ∀ g ∈ SW.img (conjClosure V H), ∀ s ∈ SW.img Lu, g * s = s * g := by
    intro g hg s hs
    obtain ⟨y, hyG, rfl⟩ := SW.mem_img.mp hg
    obtain ⟨z, hzLu, rfl⟩ := SW.mem_img.mp hs
    obtain ⟨_, hc⟩ := comm_closure_LNf SW hLuΛ hHΛ hVH hHLu hVLu hQ hyG
    exact hc z hzLu
  have hVsq' : ∀ v ∈ SW.img V, v * v = 1 := by
    intro v hv
    obtain ⟨a, haV, rfl⟩ := SW.mem_img.mp hv
    have e : (a * a : ↥Λ) = 1 := Subtype.ext (hVsq _ haV)
    rw [← map_mul, e, map_one]
  have hgen : SW.img (conjClosure V H) = Subgroup.closure
      {g | ∃ v ∈ SW.img V, ∃ x ∈ SW.img (conjClosure V H) ⊔ SW.img T, g = x * v * x⁻¹} := by
    apply le_antisymm
    · intro g hg
      obtain ⟨y, hyG, rfl⟩ := SW.mem_img.mp hg
      obtain ⟨_, hmem⟩ := gen_le_closure_LNf SW hHΛ hVH hHsup y hyG
      exact hmem
    · rw [Subgroup.closure_le]
      rintro g ⟨v, hv, u, hu, rfl⟩
      exact hsupNorm' u hu v (hVimg hv)
  have hVne' : ∃ v ∈ SW.img V, v ≠ 1 := by
    obtain ⟨v, hvV, hnot⟩ := hVne
    have hvΛ : v ∈ Λ := hVΛ hvV
    refine ⟨SW.ρ ⟨v, hvΛ⟩, SW.mem_img.mpr ⟨⟨v, hvΛ⟩, hvV, rfl⟩, ?_⟩
    intro h1
    apply hnot
    intro x hxW₁
    have hvx : v * x * v⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (SW.norm₁ hvΛ) x).mp hxW₁
    have hc : v * x * v⁻¹ * x⁻¹ ∈ W₁ := W₁.mul_mem hvx (W₁.inv_mem hxW₁)
    have key : SW.ρ ⟨v, hvΛ⟩ (toWf_LNf (SW.π ⟨x, hxW₁⟩)) - toWf_LNf (SW.π ⟨x, hxW₁⟩) =
        toWf_LNf (SW.π ⟨v * x * v⁻¹ * x⁻¹, hc⟩) :=
      SW.ρ_sub_self ⟨v, hvΛ⟩ ⟨x, hxW₁⟩ hc
    rw [h1] at key
    have h0 : toWf_LNf (SW.π ⟨v * x * v⁻¹ * x⁻¹, hc⟩) = 0 := by
      rw [← key]
      exact sub_self _
    exact (SW.ker _).mp (ofMul_eq_zero.mp h0)
  have hWBT : InvUnder (SW.img T) (SW.sub (V ⊓ W₁)) := by
    intro t ht w hw
    obtain ⟨a, haT, rfl⟩ := SW.mem_img.mp ht
    refine SW.sub_inv (V ⊓ W₁) a (fun c hc => ?_) w hw
    rw [Subgroup.mem_inf] at hc ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV haT) c).mp hc.1,
      (Subgroup.mem_normalizer_iff.mp (SW.norm₁ a.2) c).mp hc.2⟩
  have hWBV : ∀ v ∈ SW.img V, ∀ w : W, v w - w ∈ SW.sub (V ⊓ W₁) := by
    intro v hv w
    obtain ⟨a, haV, rfl⟩ := SW.mem_img.mp hv
    obtain ⟨x, hx⟩ := SW.surj (Multiplicative.ofAdd w)
    have hw : toWf_LNf (SW.π x) = w :=
      congrArg (fun q : Multiplicative W => toWf_LNf q) hx
    subst hw
    have hc : (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ ∈ W₁ :=
      W₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (SW.norm₁ a.2) (x : G)).mp x.2)
        (W₁.inv_mem x.2)
    have key : SW.ρ a (toWf_LNf (SW.π x)) - toWf_LNf (SW.π x) =
        toWf_LNf (SW.π ⟨(a : G) * x * (a : G)⁻¹ * (x : G)⁻¹, hc⟩) :=
      SW.ρ_sub_self a x hc
    have hmem : (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ ∈ V ⊓ W₁ := by
      refine Subgroup.mem_inf.mpr ⟨?_, hc⟩
      have hxa : (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hW₁V x.2) (a : G)⁻¹).mp (V.inv_mem haV)
      have e : (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ =
          (a : G) * ((x : G) * (a : G)⁻¹ * (x : G)⁻¹) := by
        group
      rw [e]
      exact V.mul_mem haV hxa
    rw [key]
    exact SW.mem_sub_of_mem hmem
  exact
    { nontrivial := hnt
      irreducible := hirr'
      comm := hcomm
      T_norm_S := hTnormS
      T_norm_G := hTnorm
      V_le := hVimg
      V_sq := hVsq'
      gen := hgen
      V_ne := hVne'
      WB_T := hWBT
      WB_V := hWBV
      hb := hb }

end CFSG.Quasithin.H13.L829N
