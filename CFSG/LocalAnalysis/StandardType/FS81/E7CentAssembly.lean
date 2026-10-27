module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentAssemblyAux
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {X : Type} [Group X]

private noncomputable def e7CentHom {Y : Subgroup X}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) :
    ↥(adjointGroup .E7 (ZMod 2)) →* X :=
  Y.subtype.comp ψ.toMonoidHom

private theorem e7CentHom_injective {Y : Subgroup X}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} : Function.Injective (e7CentHom ψ) := by
  intro a c h
  exact ψ.injective (Subtype.ext h)

private theorem e7CentHom_range {Y : Subgroup X}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} : (e7CentHom ψ).range = Y := by
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact (ψ m).2
  · intro hx
    exact ⟨ψ.symm ⟨x, hx⟩, by simp [e7CentHom]⟩

private noncomputable def e7CentT
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : X :=
  e7CentHom ψ e7HighInv

private noncomputable def e7CentH
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Subgroup X :=
  Subgroup.centralizer ({e7CentT ψ} : Set X)

private noncomputable def e7CentQ
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Subgroup X :=
  (highRadical .E7 (ZMod 2)).map (e7CentHom ψ)

private noncomputable def e7CentL
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Subgroup X :=
  (perpLevi .E7 (ZMod 2)).map (e7CentHom ψ)

private noncomputable def e7CentS1
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Subgroup X :=
  e7CentS.map (e7CentHom ψ)

private noncomputable def e7CentK1
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Subgroup X :=
  e7A1.map (e7CentHom ψ)

private noncomputable def e7CentSig
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : X :=
  e7CentHom ψ e7CentSigma

private noncomputable def e7CentBelt
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : X :=
  e7CentHom ψ e7CentB

private noncomputable def e7CentKelt
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : X :=
  e7CentHom ψ e7CentInvol

private theorem centralizer_conj_le {Y : Subgroup X} {a b y : X} (hy : y ∈ Y)
    (hyb : y * a * y⁻¹ = b) (hC : Subgroup.centralizer ({a} : Set X) ≤ Y) :
    Subgroup.centralizer ({b} : Set X) ≤ Y := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff] at hz
  have hza : (y⁻¹ * z * y) * a = a * (y⁻¹ * z * y) := by
    have hzb : z * (y * a * y⁻¹) = (y * a * y⁻¹) * z := by
      rw [← hyb] at hz
      exact hz
    calc (y⁻¹ * z * y) * a = y⁻¹ * (z * (y * a * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * a * y⁻¹) * z) * y := by rw [hzb]
      _ = a * (y⁻¹ * z * y) := by group
  have hzy : y⁻¹ * z * y ∈ Y :=
    hC (Subgroup.mem_centralizer_singleton_iff.2 hza)
  rw [show z = y * (y⁻¹ * z * y) * y⁻¹ by group]
  exact Y.mul_mem (Y.mul_mem hy hzy) (Y.inv_mem hy)

private theorem conj_eq_of_mem_zpowers {z w h : X} (hh : h * z = z * h)
    (hw : w ∈ Subgroup.zpowers z) : h * w * h⁻¹ = w := by
  have h1 : w * h = h * w :=
    Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hh.symm) hw)
  rw [← h1, mul_assoc, mul_inv_cancel, mul_one]

private theorem e7CentHY
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hQ : E7CentModelQ) :
    e7CentH ψ ⊓ Y = e7CentQ ψ ⊔ e7CentL ψ := by
  have h := centralizer_singleton_inf_range_eq_map (e7CentHom ψ)
    (e7CentHom_injective (ψ := ψ)) e7HighInv
  rw [e7CentHom_range] at h
  obtain ⟨-, hsup, -, -⟩ := hQ.2.2
  change Subgroup.centralizer ({e7CentHom ψ e7HighInv} : Set X) ⊓ Y =
    (highRadical .E7 (ZMod 2)).map (e7CentHom ψ) ⊔
      (perpLevi .E7 (ZMod 2)).map (e7CentHom ψ)
  rw [h, ← hsup, Subgroup.map_sup]

private theorem e7CentCommElem
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    {a b : ↥(adjointGroup .E7 (ZMod 2))} (h : a * b = b * a) :
    e7CentHom ψ a * e7CentHom ψ b = e7CentHom ψ b * e7CentHom ψ a := by
  simpa only [map_mul] using congrArg (e7CentHom ψ) h

private theorem e7CentCommSigma
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    {a : ↥(adjointGroup .E7 (ZMod 2))} (h : a * e7CentSigma = e7CentSigma * a) :
    e7CentHom ψ a * e7CentSig ψ = e7CentSig ψ * e7CentHom ψ a :=
  e7CentCommElem h

private theorem e7CentMemZpowers
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    {a : ↥(adjointGroup .E7 (ZMod 2))} (h : a ∈ Subgroup.zpowers e7HighInv) :
    e7CentHom ψ a ∈ Subgroup.zpowers (e7CentT ψ) := by
  have h' : e7CentHom ψ a ∈ (Subgroup.zpowers e7HighInv).map (e7CentHom ψ) :=
    Subgroup.mem_map_of_mem _ h
  rwa [MonoidHom.map_zpowers] at h'

private theorem e7CentMemZpowersOf
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    {a : ↥(adjointGroup .E7 (ZMod 2))} (h : e7CentHom ψ a ∈ Subgroup.zpowers (e7CentT ψ)) :
    a ∈ Subgroup.zpowers e7HighInv := by
  have h' : e7CentHom ψ a ∈ (Subgroup.zpowers e7HighInv).map (e7CentHom ψ) := by
    rwa [MonoidHom.map_zpowers]
  exact (Subgroup.mem_map_iff_mem (e7CentHom_injective (ψ := ψ))).1 h'

private theorem e7CentMemCommSet
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    {w : ↥(adjointGroup .E7 (ZMod 2))}
    (h : w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma) :
    e7CentHom ψ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ) := by
  have h' : e7CentHom ψ w ∈ fs81CommSet
      ((highRadical .E7 (ZMod 2)).map (e7CentHom ψ)) (e7CentHom ψ e7CentSigma) := by
    rw [fs81CommSet_map]
    exact ⟨w, h, rfl⟩
  exact h'

private structure E7CentRadicalData
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Prop where
  hQ1leH : e7CentQ ψ ≤ e7CentH ψ
  hL1leH : e7CentL ψ ≤ e7CentH ψ
  hQ1inf : e7CentQ ψ ⊓ e7CentL ψ = ⊥
  hQ1norm : e7CentH ψ ≤ Subgroup.normalizer (e7CentQ ψ : Set X)
  hL1norm : e7CentL ψ ≤ Subgroup.normalizer (e7CentQ ψ : Set X)
  hQ1p : IsPGroup 2 (e7CentQ ψ)
  hQ1cent : e7CentH ψ ⊓ Subgroup.centralizer (e7CentQ ψ : Set X) ≤ e7CentQ ψ
  ht0Q : e7CentT ψ ∈ e7CentQ ψ
  hHt0 : ∀ h ∈ e7CentH ψ, h * e7CentT ψ = e7CentT ψ * h
  hQQ : ∀ q₁ ∈ e7CentQ ψ, ∀ q₂ ∈ e7CentQ ψ, ⁅q₁, q₂⁆ ∈ Subgroup.zpowers (e7CentT ψ)
  hZcentral : ∀ h ∈ e7CentH ψ, ∀ z ∈ Subgroup.zpowers (e7CentT ψ), h * z * h⁻¹ = z

private theorem e7CentQQ
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    (hQQ0 : ∀ q₁ ∈ highRadical .E7 (ZMod 2), ∀ q₂ ∈ highRadical .E7 (ZMod 2),
      ⁅q₁, q₂⁆ ∈ Subgroup.zpowers e7HighInv) :
    ∀ q₁ ∈ e7CentQ ψ, ∀ q₂ ∈ e7CentQ ψ, ⁅q₁, q₂⁆ ∈ Subgroup.zpowers (e7CentT ψ) := by
  intro q₁ h₁ q₂ h₂
  obtain ⟨a, ha, rfl⟩ := h₁
  obtain ⟨b, hb, rfl⟩ := h₂
  simpa only [map_commutatorElement] using e7CentMemZpowers (hQQ0 a ha b hb)

private theorem e7CentRadicalFacts
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hQ : E7CentModelQ)
    (hHY : e7CentH ψ ⊓ Y = e7CentQ ψ ⊔ e7CentL ψ) (hChar : CharTwo (e7CentH ψ))
    (hCore : pCoreOf 2 (e7CentH ψ) =
      ((highRadical .E7 (ZMod 2)).map ψ.toMonoidHom).map Y.subtype) :
    E7CentRadicalData ψ := by
  obtain ⟨ht0Q0, hQQ0, hQdec⟩ := hQ
  obtain ⟨hQp, hQsup, hQinf, hQnorm⟩ := hQdec
  have hQ1core : e7CentQ ψ = pCoreOf 2 (e7CentH ψ) := by
    rw [hCore, Subgroup.map_map]
    rfl
  have hQ1leHY : e7CentQ ψ ≤ e7CentH ψ ⊓ Y := by rw [hHY]; exact le_sup_left
  have hL1leHY : e7CentL ψ ≤ e7CentH ψ ⊓ Y := by rw [hHY]; exact le_sup_right
  refine ⟨hQ1leHY.trans inf_le_left, hL1leHY.trans inf_le_left, ?_, ?_, ?_, hQp.map _, ?_,
    ?_, ?_, ?_, ?_⟩
  · change (highRadical .E7 (ZMod 2)).map (e7CentHom ψ) ⊓
      (perpLevi .E7 (ZMod 2)).map (e7CentHom ψ) = ⊥
    rw [← Subgroup.map_inf (highRadical .E7 (ZMod 2)) (perpLevi .E7 (ZMod 2))
      (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)), hQinf, Subgroup.map_bot]
  · rw [hQ1core]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (e7CentH ψ)
  · exact (Subgroup.map_mono hQnorm).trans (Subgroup.le_normalizer_map (e7CentHom ψ))
  · rw [hQ1core]
    simpa [CharTwo] using hChar
  · exact Subgroup.mem_map_of_mem _ ht0Q0
  · exact fun h hh => Subgroup.mem_centralizer_singleton_iff.1 hh
  · exact e7CentQQ hQQ0
  · exact fun h hh z hz =>
      conj_eq_of_mem_zpowers (Subgroup.mem_centralizer_singleton_iff.1 hh) hz

private structure E7CentSigmaData
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Prop where
  hσL : e7CentSig ψ ∈ e7CentL ψ
  hσH : e7CentSig ψ ∈ e7CentH ψ
  hσord : orderOf (e7CentSig ψ) = 2
  hS1H : e7CentS1 ψ ≤ e7CentH ψ
  hS1p : IsPGroup 2 (e7CentS1 ψ)
  hSσ : ∀ s ∈ e7CentS1 ψ, s * e7CentSig ψ = e7CentSig ψ * s
  hSw : ∀ s ∈ e7CentS1 ψ, ∀ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ),
    ⁅s, w⁆ ∈ Subgroup.zpowers (e7CentT ψ)
  hSQ : ∀ s ∈ e7CentS1 ψ, ∀ q ∈ e7CentQ ψ,
    ⁅⁅s, q⁆, e7CentSig ψ⁆ ∈ Subgroup.zpowers (e7CentT ψ)
  hSC : ∀ s ∈ e7CentS1 ψ, ∀ c ∈ e7CentQ ψ,
    ⁅c, e7CentSig ψ⁆ ∈ Subgroup.zpowers (e7CentT ψ) →
      ⁅s, c⁆ ∈ fs81SigmaW (e7CentQ ψ) (e7CentSig ψ) (e7CentT ψ)

private theorem e7CentSigmaWMem
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    (hSC0 : ∀ s ∈ e7CentS, ∀ c ∈ highRadical .E7 (ZMod 2),
      ⁅c, e7CentSigma⁆ ∈ Subgroup.zpowers e7HighInv →
        ⁅s, c⁆ ∈ fs81SigmaW (highRadical .E7 (ZMod 2)) e7CentSigma e7HighInv)
    {s c : ↥(adjointGroup .E7 (ZMod 2))} (hs : s ∈ e7CentS)
    (hc : c ∈ highRadical .E7 (ZMod 2))
    (hcent : ⁅e7CentHom ψ c, e7CentSig ψ⁆ ∈ Subgroup.zpowers (e7CentT ψ)) :
    ⁅e7CentHom ψ s, e7CentHom ψ c⁆ ∈
      fs81SigmaW (e7CentQ ψ) (e7CentSig ψ) (e7CentT ψ) := by
  have hcent₀ : ⁅c, e7CentSigma⁆ ∈ Subgroup.zpowers e7HighInv :=
    e7CentMemZpowersOf (by simpa only [e7CentSig, map_commutatorElement] using hcent)
  have h := hSC0 s hs c hc hcent₀
  have hmem : e7CentHom ψ ⁅s, c⁆ ∈
      (fs81SigmaW (highRadical .E7 (ZMod 2)) e7CentSigma e7HighInv).map
        (e7CentHom ψ) := Subgroup.mem_map_of_mem _ h
  rw [fs81SigmaW_map, map_commutatorElement] at hmem
  exact hmem

private theorem e7CentSigmaFacts
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hSyl : E7CentModelSylow)
    (hF : E7CentModelFlag) (R : E7CentRadicalData ψ) : E7CentSigmaData ψ := by
  obtain ⟨-, -, -, hσD, hσord0, -⟩ := hSyl
  obtain ⟨hSD, -, hSp, hSσ0, -, hSw0, -, hSQ0, hSC0⟩ := hF
  refine ⟨Subgroup.mem_map_of_mem _ hσD, R.hL1leH (Subgroup.mem_map_of_mem _ hσD),
    (orderOf_injective (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)) e7CentSigma).trans hσord0,
    (Subgroup.map_mono hSD).trans R.hL1leH, hSp.map _, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    exact e7CentCommSigma (hSσ0 s₀ hs₀)
  · intro s hs w hw
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have hw' : w ∈ (e7CentHom ψ) '' fs81CommSet
        (highRadical .E7 (ZMod 2)) e7CentSigma := by
      rw [← fs81CommSet_map]
      exact hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw'
    simpa only [map_commutatorElement] using e7CentMemZpowers (hSw0 s₀ hs₀ w₀ hw₀)
  · intro s hs q hq
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hmem := Subgroup.mem_map_of_mem (e7CentHom ψ) (hSQ0 s₀ hs₀ q₀ hq₀)
    rw [MonoidHom.map_zpowers, map_commutatorElement, map_commutatorElement] at hmem
    exact hmem
  · intro s hs c hc hcent
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact e7CentSigmaWMem hSC0 hs₀ hc₀ hcent

private structure E7CentKData
    {Y : Subgroup X} (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : Prop where
  hK1H : e7CentK1 ψ ≤ e7CentH ψ
  hKnormS : e7CentK1 ψ ≤ Subgroup.normalizer (e7CentS1 ψ : Set X)
  hKσ : ∀ x ∈ e7CentK1 ψ, x * e7CentSig ψ = e7CentSig ψ * x
  hKw : ∀ x ∈ e7CentK1 ψ, ∀ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ),
    ⁅x, w⁆ ∈ Subgroup.zpowers (e7CentT ψ)
  hbK : e7CentBelt ψ ∈ e7CentK1 ψ
  hkK : e7CentKelt ψ ∈ e7CentK1 ψ
  hborder : orderOf (e7CentBelt ψ) = 3
  hkorder : orderOf (e7CentKelt ψ) = 2
  hkbk : e7CentKelt ψ * e7CentBelt ψ * (e7CentKelt ψ)⁻¹ = (e7CentBelt ψ)⁻¹
  hKclosure : e7CentK1 ψ ≤ Subgroup.closure ({e7CentBelt ψ, e7CentKelt ψ} : Set X)

private theorem e7CentKFacts
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hK : E7CentModelK)
    (hF : E7CentModelFlag) (hJ : E7CentModelJ) (R : E7CentRadicalData ψ) :
    E7CentKData ψ := by
  obtain ⟨hbK0, hkK0, hborder0, hkorder0, hkbk0, hKclos0, -⟩ := hK
  obtain ⟨-, hKD, -, -, hKσ0, -, hKw0, -, -⟩ := hF
  obtain ⟨-, -, -, hKNS, -⟩ := hJ
  refine ⟨(Subgroup.map_mono hKD).trans R.hL1leH,
    (Subgroup.map_mono hKNS).trans (Subgroup.le_normalizer_map (e7CentHom ψ)), ?_, ?_,
    Subgroup.mem_map_of_mem _ hbK0, Subgroup.mem_map_of_mem _ hkK0, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    exact e7CentCommSigma (hKσ0 x₀ hx₀)
  · intro x hx w hw
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hw' : w ∈ (e7CentHom ψ) '' fs81CommSet
        (highRadical .E7 (ZMod 2)) e7CentSigma := by
      rw [← fs81CommSet_map]
      exact hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw'
    simpa only [map_commutatorElement] using e7CentMemZpowers (hKw0 x₀ hx₀ w₀ hw₀)
  · exact (orderOf_injective (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)) e7CentB).trans hborder0
  · exact (orderOf_injective (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)) e7CentInvol).trans
      hkorder0
  · simpa only [e7CentKelt, e7CentBelt, map_mul, map_inv] using
      congrArg (e7CentHom ψ) hkbk0
  · have h := Subgroup.map_mono (f := e7CentHom ψ) hKclos0
    rwa [MonoidHom.map_closure, Set.image_pair] at h

private theorem e7CentCb
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    {r : ↥(adjointGroup .E7 (ZMod 2))} (hK : E7CentModelK)
    (hCY : Subgroup.centralizer ({e7CentHom ψ r} : Set X) ≤ Y)
    (hrJ : r ∈ e7JTheta) (hr3 : orderOf r = 3) :
    Subgroup.centralizer ({e7CentBelt ψ} : Set X) ≤ Y := by
  obtain ⟨-, -, -, -, -, -, hconj⟩ := hK
  obtain ⟨g, hg⟩ := hconj r hrJ hr3
  have hgY : e7CentHom ψ g ∈ Y := (ψ g).2
  have hconj' : e7CentHom ψ g * e7CentHom ψ r * (e7CentHom ψ g)⁻¹ = e7CentBelt ψ := by
    have h1 : e7CentHom ψ g * e7CentHom ψ r * (e7CentHom ψ g)⁻¹ =
        e7CentHom ψ (g * r * g⁻¹) := by
      simp only [map_mul, map_inv]
    rw [h1, hg]
    rfl
  exact centralizer_conj_le hgY hconj' hCY

private theorem e7CentPExists
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hP : E7CentModelP)
    (hJ : E7CentModelJ) (R : E7CentRadicalData ψ) (hK : E7CentModelK)
    (hCb : Subgroup.centralizer ({e7CentBelt ψ} : Set X) ≤ Y) :
    ∃ (P₁ : Subgroup X) (b₁ : X), P₁ ≤ e7CentH ψ ∧
      Nonempty (↥P₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧ b₁ ∈ P₁ ∧
      orderOf b₁ = 3 ∧ P₁ ≤ Subgroup.normalizer (e7CentS1 ψ : Set X) ∧
      (∀ p ∈ P₁, p * e7CentSig ψ = e7CentSig ψ * p) ∧
      (∀ p ∈ P₁, p * e7CentKelt ψ = e7CentKelt ψ * p) ∧
      Subgroup.centralizer ({b₁} : Set X) ≤ Y := by
  obtain ⟨P, hPD4, hPiso, b₁₀, hb₁P, gP, hgP⟩ := hP
  obtain ⟨hD4D, hD4σ, hD4K, -, hD4NS⟩ := hJ
  obtain ⟨hbK0, hkK0, hborder0, -, -, -, -⟩ := hK
  refine ⟨P.map (e7CentHom ψ), e7CentHom ψ b₁₀,
    (Subgroup.map_mono (hPD4.trans hD4D)).trans R.hL1leH, ?_,
    Subgroup.mem_map_of_mem _ hb₁P, ?_,
    (Subgroup.map_mono (hPD4.trans hD4NS)).trans (Subgroup.le_normalizer_map (e7CentHom ψ)),
    ?_, ?_, ?_⟩
  · obtain ⟨eP⟩ := hPiso
    exact ⟨(Subgroup.equivMapOfInjective P (e7CentHom ψ)
      (e7CentHom_injective (ψ := ψ))).symm.trans eP⟩
  · have hsem : SemiconjBy gP e7CentB b₁₀ := by
      show gP * e7CentB = b₁₀ * gP
      rw [← hgP]
      group
    exact (orderOf_injective (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)) b₁₀).trans
      ((SemiconjBy.orderOf_eq gP hsem).symm.trans hborder0)
  · intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    exact e7CentCommSigma (hD4σ p₀ (hPD4 hp₀))
  · intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    exact e7CentCommElem (hD4K p₀ (hPD4 hp₀) e7CentInvol hkK0)
  · have hconj : e7CentHom ψ gP * e7CentBelt ψ * (e7CentHom ψ gP)⁻¹ =
        e7CentHom ψ b₁₀ := by
      have h1 : e7CentHom ψ gP * e7CentBelt ψ * (e7CentHom ψ gP)⁻¹ =
          e7CentHom ψ (gP * e7CentB * gP⁻¹) := by
        simp only [e7CentBelt, map_mul, map_inv]
      rw [h1, hgP]
    exact centralizer_conj_le (ψ gP).2 hconj hCb

private theorem e7CentStepSixCentralize
    {Y : Subgroup X}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (R : E7CentRadicalData ψ)
    (Sg : E7CentSigmaData ψ) {q : X} (hq : q ∈ e7CentQ ψ)
    {d : ↥(adjointGroup .E7 (ZMod 2))} (hdD : d ∈ perpLevi .E7 (ZMod 2))
    (hcomm : ⁅e7CentHom ψ d * q, e7CentSig ψ⁆ ∈ e7CentQ ψ) :
    d * e7CentSigma = e7CentSigma * d := by
  have hιdL : e7CentHom ψ d ∈ e7CentL ψ := Subgroup.mem_map_of_mem _ hdD
  have hιdH : e7CentHom ψ d ∈ e7CentH ψ := R.hL1leH hιdL
  have hqcomm : ⁅q, e7CentSig ψ⁆ ∈ e7CentQ ψ := by
    have hq' : e7CentSig ψ * q⁻¹ * (e7CentSig ψ)⁻¹ ∈ e7CentQ ψ :=
      (Subgroup.mem_normalizer_iff.1 (R.hQ1norm Sg.hσH) q⁻¹).1 ((e7CentQ ψ).inv_mem hq)
    have h2 : q * (e7CentSig ψ * q⁻¹ * (e7CentSig ψ)⁻¹) ∈ e7CentQ ψ :=
      (e7CentQ ψ).mul_mem hq hq'
    simpa only [commutatorElement_def, mul_assoc] using h2
  have hcommd : ⁅e7CentHom ψ d, e7CentSig ψ⁆ ∈ e7CentQ ψ := by
    have h1 : e7CentHom ψ d * ⁅q, e7CentSig ψ⁆ * (e7CentHom ψ d)⁻¹ ∈ e7CentQ ψ :=
      (Subgroup.mem_normalizer_iff.1 (R.hQ1norm hιdH) ⁅q, e7CentSig ψ⁆).1 hqcomm
    have h2 : ⁅e7CentHom ψ d * q, e7CentSig ψ⁆ =
        e7CentHom ψ d * ⁅q, e7CentSig ψ⁆ * (e7CentHom ψ d)⁻¹ *
          ⁅e7CentHom ψ d, e7CentSig ψ⁆ :=
      commutatorElement_mul_left_eq_conj_mul _ _ _
    have h3 : ⁅e7CentHom ψ d, e7CentSig ψ⁆ =
        (e7CentHom ψ d * ⁅q, e7CentSig ψ⁆ * (e7CentHom ψ d)⁻¹)⁻¹ *
          ⁅e7CentHom ψ d * q, e7CentSig ψ⁆ := by
      rw [h2]
      group
    rw [h3]
    exact (e7CentQ ψ).mul_mem ((e7CentQ ψ).inv_mem h1) hcomm
  have hzero : ⁅e7CentHom ψ d, e7CentSig ψ⁆ = 1 := by
    have hcL : ⁅e7CentHom ψ d, e7CentSig ψ⁆ ∈ e7CentL ψ :=
      (e7CentL ψ).mul_mem ((e7CentL ψ).mul_mem ((e7CentL ψ).mul_mem hιdL Sg.hσL)
        ((e7CentL ψ).inv_mem hιdL)) ((e7CentL ψ).inv_mem Sg.hσL)
    have hmem : ⁅e7CentHom ψ d, e7CentSig ψ⁆ ∈ e7CentQ ψ ⊓ e7CentL ψ :=
      Subgroup.mem_inf.mpr ⟨hcommd, hcL⟩
    rw [R.hQ1inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  apply e7CentHom_injective (ψ := ψ)
  show e7CentHom ψ (d * e7CentSigma) = e7CentHom ψ (e7CentSigma * d)
  rw [map_mul, map_mul]
  exact commutatorElement_eq_one_iff_mul_comm.mp hzero

private theorem e7CentQQCommSet
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (R : E7CentRadicalData ψ)
    (Sg : E7CentSigmaData ψ) {q : X} (hq : q ∈ e7CentQ ψ)
    {w : ↥(adjointGroup .E7 (ZMod 2))}
    (hw : w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma) :
    ⁅q, e7CentHom ψ w⁆ ∈ Subgroup.zpowers (e7CentT ψ) := by
  obtain ⟨q₂, hq₂, rfl⟩ := hw
  have hq₂' : e7CentHom ψ q₂ ∈ e7CentQ ψ := Subgroup.mem_map_of_mem _ hq₂
  have hιwQ : e7CentHom ψ ⁅q₂, e7CentSigma⁆ ∈ e7CentQ ψ := by
    have h1 : e7CentSig ψ * (e7CentHom ψ q₂)⁻¹ * (e7CentSig ψ)⁻¹ ∈ e7CentQ ψ :=
      (Subgroup.mem_normalizer_iff.1 (R.hQ1norm Sg.hσH) (e7CentHom ψ q₂)⁻¹).1
        ((e7CentQ ψ).inv_mem hq₂')
    have h2 : e7CentHom ψ q₂ *
        (e7CentSig ψ * (e7CentHom ψ q₂)⁻¹ * (e7CentSig ψ)⁻¹) ∈ e7CentQ ψ :=
      (e7CentQ ψ).mul_mem hq₂' h1
    have h2' : ⁅e7CentHom ψ q₂, e7CentSig ψ⁆ ∈ e7CentQ ψ := by
      simpa only [commutatorElement_def, mul_assoc] using h2
    simpa only [e7CentSig, map_commutatorElement] using h2'
  exact R.hQQ q hq _ hιwQ

private theorem e7CentStepSixCommutator
    {Y : Subgroup X}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (R : E7CentRadicalData ψ)
    (Sg : E7CentSigmaData ψ) {q : X} (hq : q ∈ e7CentQ ψ)
    {d : ↥(adjointGroup .E7 (ZMod 2))} (hdD : d ∈ perpLevi .E7 (ZMod 2))
    (hcent : ∀ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ),
      ⁅e7CentHom ψ d * q, w⁆ ∈ Subgroup.zpowers (e7CentT ψ)) :
    ∀ w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma,
      ⁅d, w⁆ ∈ Subgroup.zpowers e7HighInv := by
  have hιdH : e7CentHom ψ d ∈ e7CentH ψ :=
    R.hL1leH (Subgroup.mem_map_of_mem _ hdD)
  intro w hw
  have hW : e7CentHom ψ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ) :=
    e7CentMemCommSet hw
  have hgiven : ⁅e7CentHom ψ d * q, e7CentHom ψ w⁆ ∈ Subgroup.zpowers (e7CentT ψ) :=
    hcent _ hW
  have hqW : ⁅q, e7CentHom ψ w⁆ ∈ Subgroup.zpowers (e7CentT ψ) :=
    e7CentQQCommSet R Sg hq hw
  have hqW' : e7CentHom ψ d * ⁅q, e7CentHom ψ w⁆ * (e7CentHom ψ d)⁻¹ ∈
      Subgroup.zpowers (e7CentT ψ) := by
    rw [R.hZcentral (e7CentHom ψ d) hιdH _ hqW]
    exact hqW
  have h2 : ⁅e7CentHom ψ d * q, e7CentHom ψ w⁆ =
      (e7CentHom ψ d * ⁅q, e7CentHom ψ w⁆ * (e7CentHom ψ d)⁻¹) *
        ⁅e7CentHom ψ d, e7CentHom ψ w⁆ :=
    commutatorElement_mul_left_eq_conj_mul _ _ _
  have h3 : ⁅e7CentHom ψ d, e7CentHom ψ w⁆ =
      (e7CentHom ψ d * ⁅q, e7CentHom ψ w⁆ * (e7CentHom ψ d)⁻¹)⁻¹ *
        ⁅e7CentHom ψ d * q, e7CentHom ψ w⁆ := by
    rw [h2]
    group
  have h4 : ⁅e7CentHom ψ d, e7CentHom ψ w⁆ ∈ Subgroup.zpowers (e7CentT ψ) := by
    rw [h3]
    exact (Subgroup.zpowers (e7CentT ψ)).mul_mem
      ((Subgroup.zpowers (e7CentT ψ)).inv_mem hqW') hgiven
  have h5 : e7CentHom ψ ⁅d, w⁆ ∈ (Subgroup.zpowers e7HighInv).map (e7CentHom ψ) := by
    rw [MonoidHom.map_zpowers, map_commutatorElement]
    exact h4
  exact (Subgroup.mem_map_iff_mem (e7CentHom_injective (ψ := ψ))).1 h5

private theorem e7CentStepSix
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    (hHY : e7CentH ψ ⊓ Y = e7CentQ ψ ⊔ e7CentL ψ) (R : E7CentRadicalData ψ)
    (Sg : E7CentSigmaData ψ) (hMM : E7CentModelM) :
    ∀ h ∈ e7CentH ψ ⊓ Y, ⁅h, e7CentSig ψ⁆ ∈ e7CentQ ψ →
      (∀ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ),
        ⁅h, w⁆ ∈ Subgroup.zpowers (e7CentT ψ)) →
      h ∈ e7CentQ ψ ⊔ e7CentS1 ψ ⊔ e7CentK1 ψ := by
  intro h hh hcomm hcent
  have h1 : h ∈ e7CentQ ψ ⊔ e7CentL ψ := hHY ▸ hh
  have hsplit : h ∈ e7CentL ψ ⊔ e7CentQ ψ := by rwa [sup_comm] at h1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (e7CentL ψ)
    (e7CentQ ψ) R.hL1norm, Set.mem_mul] at hsplit
  obtain ⟨l, hl, q, hq, rfl⟩ := hsplit
  obtain ⟨d, hdD, rfl⟩ := hl
  have hdSK : d ∈ e7CentS ⊔ e7A1 :=
    hMM d hdD (e7CentStepSixCentralize R Sg hq hdD hcomm)
      (e7CentStepSixCommutator R Sg hq hdD hcent)
  have hιdSK : e7CentHom ψ d ∈ e7CentS1 ψ ⊔ e7CentK1 ψ := by
    have h := Subgroup.mem_map_of_mem (e7CentHom ψ) hdSK
    rwa [Subgroup.map_sup] at h
  have hmul' : e7CentHom ψ d * q ∈ (e7CentS1 ψ ⊔ e7CentK1 ψ) ⊔ e7CentQ ψ :=
    Subgroup.mul_mem_sup hιdSK hq
  have hle : (e7CentS1 ψ ⊔ e7CentK1 ψ) ⊔ e7CentQ ψ ≤
      e7CentQ ψ ⊔ e7CentS1 ψ ⊔ e7CentK1 ψ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
    · exact le_sup_left.trans le_sup_left
  exact hle hmul'

private theorem e7CentExistsM
    [Finite X] {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hM : FS81CentM)
    (R : E7CentRadicalData ψ) (Sg : E7CentSigmaData ψ) (Kd : E7CentKData ψ)
    (P₁ : Subgroup X) (b₁ : X) (hP1H : P₁ ≤ e7CentH ψ)
    (hPiso : Nonempty (↥P₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hb₁P : b₁ ∈ P₁) (hb₁ord : orderOf b₁ = 3)
    (hPnormS : P₁ ≤ Subgroup.normalizer (e7CentS1 ψ : Set X))
    (hPσ : ∀ p ∈ P₁, p * e7CentSig ψ = e7CentSig ψ * p)
    (hPk : ∀ p ∈ P₁, p * e7CentKelt ψ = e7CentKelt ψ * p)
    (hCb : Subgroup.centralizer ({e7CentBelt ψ} : Set X) ≤ Y)
    (hCb₁ : Subgroup.centralizer ({b₁} : Set X) ≤ Y)
    (hMY : ∀ h ∈ e7CentH ψ ⊓ Y, ⁅h, e7CentSig ψ⁆ ∈ e7CentQ ψ →
      (∀ w ∈ fs81CommSet (e7CentQ ψ) (e7CentSig ψ),
        ⁅h, w⁆ ∈ Subgroup.zpowers (e7CentT ψ)) →
      h ∈ e7CentQ ψ ⊔ e7CentS1 ψ ⊔ e7CentK1 ψ) :
    ∃ M : Subgroup X, e7CentK1 ψ ≤ M ∧ M ≤ e7CentQ ψ ⊔ e7CentS1 ψ ⊔ e7CentK1 ψ ∧
      ∀ c ∈ e7CentH ψ, ⁅c, e7CentSig ψ⁆ ∈ e7CentQ ψ → ∀ m ∈ M, c * m * c⁻¹ ∈ M :=
  hM X Y (e7CentH ψ) (e7CentQ ψ) (e7CentS1 ψ) (e7CentK1 ψ) P₁
    (e7CentT ψ) (e7CentSig ψ) (e7CentBelt ψ) (e7CentKelt ψ) b₁
    R.hQ1leH R.hQ1norm R.hQ1p R.hQ1cent R.ht0Q R.hHt0 R.hQQ Sg.hσH Sg.hS1H Sg.hS1p
    Sg.hSσ Sg.hSw Sg.hSQ Sg.hSC Kd.hK1H Kd.hKnormS Kd.hKσ Kd.hKw Kd.hbK Kd.hkK
    Kd.hborder Kd.hkorder Kd.hkbk Kd.hKclosure hP1H hPiso hPσ hPk hPnormS hb₁P hb₁ord
    hCb hCb₁ hMY

private theorem e7CentControlConj
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hK : E7CentModelK)
    {r : ↥(adjointGroup .E7 (ZMod 2))} (hrJ : r ∈ e7JTheta) (hr3 : orderOf r = 3) :
    ∃ gK : ↥(adjointGroup .E7 (ZMod 2)), gK * r * gK⁻¹ = e7CentB ∧
      e7CentHom ψ gK * e7CentHom ψ r * (e7CentHom ψ gK)⁻¹ = e7CentBelt ψ := by
  obtain ⟨-, -, -, -, -, -, hconj⟩ := hK
  obtain ⟨gK, hgK⟩ := hconj r hrJ hr3
  refine ⟨gK, hgK, ?_⟩
  have h1 : e7CentHom ψ gK * e7CentHom ψ r * (e7CentHom ψ gK)⁻¹ =
      e7CentHom ψ (gK * r * gK⁻¹) := by
    simp only [map_mul, map_inv]
  rw [h1, hgK]
  rfl

private theorem e7CentControlInv
    {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} (hF : E7CentModelFlag)
    (hInv : E7CentModelInv) (hbK0 : e7CentB ∈ e7A1)
    (gK r : ↥(adjointGroup .E7 (ZMod 2))) (hgK : gK * r * gK⁻¹ = e7CentB) :
    ∀ τ ∈ e7CentL ψ, orderOf τ = 2 →
      ∃ y ∈ Y, y * e7CentHom ψ r * y⁻¹ ∈ e7CentL ψ ∧
        τ * (y * e7CentHom ψ r * y⁻¹) = (y * e7CentHom ψ r * y⁻¹) * τ := by
  obtain ⟨-, hKD, -, -, -, -, -, -, -⟩ := hF
  intro τ hτ hτ2
  obtain ⟨τ₀, hτ₀D, rfl⟩ := hτ
  have hτ₀2 : orderOf τ₀ = 2 := by
    have h := orderOf_injective (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)) τ₀
    rw [h] at hτ2
    exact hτ2
  obtain ⟨g, hgD, hgc⟩ := hInv τ₀ hτ₀D hτ₀2
  have hy : e7CentHom ψ (g * gK) * e7CentHom ψ r * (e7CentHom ψ (g * gK))⁻¹ =
      e7CentHom ψ (g * e7CentB * g⁻¹) := by
    have h1 : e7CentHom ψ (g * gK) * e7CentHom ψ r *
        (e7CentHom ψ (g * gK))⁻¹ = e7CentHom ψ (g * (gK * r * gK⁻¹) * g⁻¹) := by
      simp only [map_mul, map_inv]
      group
    rw [h1, hgK]
  refine ⟨e7CentHom ψ (g * gK), (ψ (g * gK)).2, ?_, ?_⟩
  · rw [hy]
    exact Subgroup.mem_map_of_mem _ ((perpLevi .E7 (ZMod 2)).mul_mem
      ((perpLevi .E7 (ZMod 2)).mul_mem hgD (hKD hbK0))
      ((perpLevi .E7 (ZMod 2)).inv_mem hgD))
  · rw [hy]
    show e7CentHom ψ τ₀ * e7CentHom ψ (g * e7CentB * g⁻¹) =
      e7CentHom ψ (g * e7CentB * g⁻¹) * e7CentHom ψ τ₀
    rw [← map_mul, ← map_mul]
    exact congrArg _ hgc

private theorem e7CentControl
    [Finite X] {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    (hCtl : FS81CentControl) (hF : E7CentModelFlag) (hK : E7CentModelK)
    (hInv : E7CentModelInv) (R : E7CentRadicalData ψ) (Sg : E7CentSigmaData ψ)
    (hHY : e7CentH ψ ⊓ Y = e7CentQ ψ ⊔ e7CentL ψ) (M : Subgroup X)
    (hKM : e7CentK1 ψ ≤ M)
    (hMnorm : ∀ c ∈ e7CentH ψ, ⁅c, e7CentSig ψ⁆ ∈ e7CentQ ψ → ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hMYle : M ≤ Y) {r : ↥(adjointGroup .E7 (ZMod 2))} (hrJ : r ∈ e7JTheta)
    (hr3 : orderOf r = 3) (hStrong : ∀ g : X, g * e7CentHom ψ r * g⁻¹ ∈ Y → g ∈ Y) :
    ∀ h ∈ e7CentH ψ, h * e7CentSig ψ * h⁻¹ ∈ e7CentL ψ ⊔ e7CentQ ψ →
      h ∈ e7CentL ψ ⊔ e7CentQ ψ := by
  have hbK0 : e7CentB ∈ e7A1 := hK.1
  obtain ⟨gK, hgK, hgK'⟩ := e7CentControlConj (ψ := ψ) hK hrJ hr3
  refine hCtl X Y (e7CentH ψ) (e7CentQ ψ) (e7CentL ψ) M (e7CentSig ψ)
    (e7CentHom ψ r) R.hQ1leH R.hQ1norm R.hL1leH (by rw [inf_comm]; exact R.hQ1inf)
    (le_of_eq (hHY.trans (sup_comm (e7CentQ ψ) (e7CentL ψ)))) Sg.hσL Sg.hσord hStrong
    hMYle hMnorm ⟨e7CentHom ψ gK, (ψ gK).2, by
      rw [hgK']
      exact hKM (Subgroup.mem_map_of_mem _ hbK0)⟩
    (e7CentControlInv (ψ := ψ) hF hInv hbK0 gK r hgK)

private theorem e7CentQuot
    [Finite X] {Y : Subgroup X} {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y}
    (hQuot : FS81HoltQuot) (hSyl : E7CentModelSylow) (R : E7CentRadicalData ψ)
    (Sg : E7CentSigmaData ψ) (hHY : e7CentH ψ ⊓ Y = e7CentQ ψ ⊔ e7CentL ψ)
    (hcontrol : ∀ h ∈ e7CentH ψ, h * e7CentSig ψ * h⁻¹ ∈ e7CentL ψ ⊔ e7CentQ ψ →
      h ∈ e7CentL ψ ⊔ e7CentQ ψ) :
    e7CentH ψ ≤ Y := by
  obtain ⟨hDsimple, hDna, hDfact, -, -, U, hUsyl, hσU, hUcent⟩ := hSyl
  have hU₁syl : IsSylow2In (U.map (e7CentHom ψ)) (e7CentL ψ) :=
    isSylow2In_map_of_injective (e7CentHom ψ) (e7CentHom_injective (ψ := ψ)) hUsyl
  let e := Subgroup.equivMapOfInjective (perpLevi .E7 (ZMod 2)) (e7CentHom ψ)
    (e7CentHom_injective (ψ := ψ))
  have hSimple : IsSimpleGroup ↥(e7CentL ψ) := e.symm.isSimpleGroup
  obtain ⟨a, c, hac⟩ := hDna
  have hNa : ∃ a c : ↥(e7CentL ψ), a * c ≠ c * a := by
    refine ⟨e a, e c, fun h => hac (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hcard : Nat.card ↥(e7CentL ψ) = Nat.card ↥(perpLevi .E7 (ZMod 2)) :=
    Subgroup.card_map_of_injective (K := perpLevi .E7 (ZMod 2)) (f := e7CentHom ψ)
      (e7CentHom_injective (ψ := ψ))
  have hfact : ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥(e7CentL ψ) ≠ (2 * m).factorial := by
    intro m hm
    rw [hcard]
    exact hDfact m hm
  have hHle : e7CentH ψ ≤ e7CentL ψ ⊔ e7CentQ ψ :=
    hQuot X (e7CentH ψ) (e7CentQ ψ) (e7CentL ψ) (U.map (e7CentHom ψ)) (e7CentSig ψ)
      R.hQ1leH R.hQ1norm R.hL1leH (by rw [inf_comm]; exact R.hQ1inf) hSimple hNa hfact
      hU₁syl (Subgroup.mem_map_of_mem _ hσU) Sg.hσord
      (fun s hs => by
        obtain ⟨s₀, hs₀, rfl⟩ := hs
        simpa only [e7CentSig, map_mul] using congrArg (e7CentHom ψ) (hUcent s₀ hs₀))
      hcontrol
  calc e7CentH ψ ≤ e7CentL ψ ⊔ e7CentQ ψ := hHle
    _ = e7CentH ψ ⊓ Y := (hHY.trans (sup_comm (e7CentQ ψ) (e7CentL ψ))).symm
    _ ≤ Y := inf_le_right

theorem e7RootCentStep_of_pieces
    (hQuot : FS81HoltQuot) (hCtl : FS81CentControl) (hM : FS81CentM)
    (hSyl : E7CentModelSylow) (hQ : E7CentModelQ) (hF : E7CentModelFlag) (hJ : E7CentModelJ)
    (hMM : E7CentModelM) (hK : E7CentModelK) (hP : E7CentModelP) (hInv : E7CentModelInv) :
    E7RootCentStep := by
  intro X _ _ Y ψ r hrJ hr3 hCY hStrong hChar hCore
  change e7CentH ψ ≤ Y
  have hHY := e7CentHY (ψ := ψ) hQ
  have R := e7CentRadicalFacts hQ hHY hChar hCore
  have Sg := e7CentSigmaFacts hSyl hF R
  have Kd := e7CentKFacts hK hF hJ R
  have hCb := e7CentCb hK hCY hrJ hr3
  obtain ⟨P₁, b₁, hP1H, hPiso, hb₁P, hb₁ord, hPnormS, hPσ, hPk, hCb₁⟩ :=
    e7CentPExists hP hJ R hK hCb
  have hMY := e7CentStepSix hHY R Sg hMM
  obtain ⟨M, hKM, hMSK, hMnorm⟩ :=
    e7CentExistsM hM R Sg Kd P₁ b₁ hP1H hPiso hb₁P hb₁ord hPnormS hPσ hPk hCb hCb₁ hMY
  have hQ1Y : e7CentQ ψ ≤ Y :=
    (Subgroup.map_le_range (e7CentHom ψ) _).trans (le_of_eq (e7CentHom_range (ψ := ψ)))
  have hS1Y : e7CentS1 ψ ≤ Y :=
    (Subgroup.map_le_range (e7CentHom ψ) _).trans (le_of_eq (e7CentHom_range (ψ := ψ)))
  have hK1Y : e7CentK1 ψ ≤ Y :=
    (Subgroup.map_le_range (e7CentHom ψ) _).trans (le_of_eq (e7CentHom_range (ψ := ψ)))
  have hMYle : M ≤ Y := hMSK.trans (sup_le (sup_le hQ1Y hS1Y) hK1Y)
  exact e7CentQuot hQuot hSyl R Sg hHY
    (e7CentControl hCtl hF hK hInv R Sg hHY M hKM hMnorm hMYle hrJ hr3 hStrong)

end CFSG.StandardType.FrameRoute.FS81
