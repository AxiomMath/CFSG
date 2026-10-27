module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

namespace FFC

namespace ProdSplit

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] {G G₁ G₂ : Subgroup (MulAut V)}

theorem stab (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) : G₂ ≤ stabSub (fixV G₁) := by
  intro b hb v
  constructor
  · intro hv a ha
    have h1 : a * b = b * a := hcomm a ha b hb
    have h2 : a (b v) = b v := hv a ha
    have h3 : b (a v) = b v := by
      have := congrArg (fun x : MulAut V => x v) h1
      simpa [MulAut.mul_apply] using this.symm.trans h2
    exact b.injective h3
  · intro hv a ha
    have h1 : a * b = b * a := hcomm a ha b hb
    have := congrArg (fun x : MulAut V => x v) h1
    simp only [MulAut.mul_apply] at this
    rw [this, hv a ha]

theorem res_mem (hsup : G₁ ⊔ G₂ = G) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    ∀ g ∈ G, ∃ b ∈ G₂, ∀ v ∈ fixV G₁, g v = b v := by
  intro g hg
  rw [← hsup, Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ha | hb
    · exact ⟨1, G₂.one_mem, fun v hv => by rw [hv x ha]; rfl⟩
    · exact ⟨x, hb, fun v _ => rfl⟩
  | one => exact ⟨1, G₂.one_mem, fun v _ => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b₁, hb₁, h₁⟩ := hx
    obtain ⟨b₂, hb₂, h₂⟩ := hy
    refine ⟨b₁ * b₂, G₂.mul_mem hb₁ hb₂, fun v hv => ?_⟩
    have hbv : b₂ v ∈ fixV G₁ := (stab hcomm hb₂ v).2 hv
    show x (y v) = b₁ (b₂ v)
    rw [h₂ v hv, h₁ _ hbv]
  | inv x _ hx =>
    obtain ⟨b, hb, hxb⟩ := hx
    refine ⟨b⁻¹, G₂.inv_mem hb, fun v hv => ?_⟩
    have hbv : b⁻¹ v ∈ fixV G₁ := (stab hcomm (G₂.inv_mem hb) v).2 hv
    have h1 : x (b⁻¹ v) = b (b⁻¹ v) := hxb _ hbv
    have h2 : b (b⁻¹ v) = v := by simp
    rw [h2] at h1
    show x⁻¹ v = b⁻¹ v
    apply x.injective
    rw [h1]
    simp

theorem stab_G (hsup : G₁ ⊔ G₂ = G) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    G ≤ stabSub (fixV G₁) := by
  intro g hg u
  obtain ⟨b, hb, hgb⟩ := res_mem hsup hcomm g hg
  obtain ⟨b', hb', hgb'⟩ := res_mem hsup hcomm g⁻¹ (G.inv_mem hg)
  constructor
  · intro hu
    have : u = g⁻¹ (g u) := by simp
    rw [this, hgb' _ hu]
    exact (stab hcomm hb' _).2 hu
  · intro hu
    rw [hgb u hu]
    exact (stab hcomm hb u).2 hu

theorem autSub_sup_eq (hsup : G₁ ⊔ G₂ = G) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    autSub G (fixV G₁) = autSub G₂ (fixV G₁) := by
  refine le_antisymm ?_ (autSub_mono (hsup ▸ le_sup_right) _)
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  obtain ⟨b, hb, hgb⟩ := res_mem hsup hcomm g hg
  refine mem_autSub.2 ⟨⟨b, stab hcomm hb⟩, hb, ?_⟩
  ext v
  exact (hgb v v.2).symm

end ProdSplit

end FFC

end CFSG.Quasithin
