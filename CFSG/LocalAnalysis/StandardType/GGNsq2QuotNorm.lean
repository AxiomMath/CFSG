module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotHyp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.CoprimeKernel

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.exists_normalizer_correction (hD : Datum p N f L Bs Z) (n0 : ↥N)
    (hconj : ∀ b : ↥N, (b : G) ∈ Bs → ∃ b' : ↥N, (b' : G) ∈ Bs ∧ f b' = f (n0 * b * n0⁻¹)) :
    ∃ z : ↥N, z ∈ f.ker ∧ (((z⁻¹ * n0 : ↥N)) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  set Bs' : Subgroup ↥N := Bs.subgroupOf N with hBs'
  set c : ↥N →* ↥N := (MulAut.conj n0).toMonoidHom with hc
  have hcb : ∀ b : ↥N, c b = n0 * b * n0⁻¹ := fun b => rfl
  have hcinj : Function.Injective c := (MulAut.conj n0).injective
  have hkerc : f.ker.map c = f.ker := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact (MonoidHom.normal_ker f).conj_mem _ hk n0
    · intro k hk
      refine ⟨n0⁻¹ * k * n0, ?_, ?_⟩
      · have := (MonoidHom.normal_ker f).conj_mem _ hk n0⁻¹
        simpa using this
      · rw [hcb]
        group
  have hKS : f.ker ⊓ Bs' = ⊥ := by
    rw [inf_comm]
    exact inf_ker_eq_bot_of_coprime (hD.coprime le_rfl)
  have hKHnorm : f.ker ⊔ Bs' ≤ Subgroup.normalizer (f.ker : Set ↥N) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcop : Nat.Coprime (Nat.card f.ker) (f.ker.relIndex (f.ker ⊔ Bs')) := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hKS, Subgroup.relIndex_bot_left]
    exact hD.coprime le_rfl
  have hS'H : Bs'.map c ≤ f.ker ⊔ Bs' := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨b', hb', hfb⟩ := hconj b hb
    have hk : b'⁻¹ * (n0 * b * n0⁻¹) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, inv_mul_cancel]
    have e : n0 * b * n0⁻¹ = b' * (b'⁻¹ * (n0 * b * n0⁻¹)) := by group
    rw [hcb, e]
    exact mul_mem (Subgroup.mem_sup_right hb') (Subgroup.mem_sup_left hk)
  have hKS' : f.ker ⊓ Bs'.map c = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzk, b, hb, rfl⟩
    have hb1 : b ∈ f.ker := by
      have h1 := (MonoidHom.normal_ker f).conj_mem _ hzk n0⁻¹
      have e : n0⁻¹ * c b * n0⁻¹⁻¹ = b := by rw [hcb]; group
      rwa [e] at h1
    have hb2 : b ∈ f.ker ⊓ Bs' := ⟨hb1, hb⟩
    rw [hKS] at hb2
    have hb0 : b = 1 := Subgroup.mem_bot.1 hb2
    rw [hb0, map_one]
    exact Subgroup.one_mem _
  have hKsupS' : f.ker ⊔ Bs'.map c = f.ker ⊔ Bs' := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hS'H)
    have h1 : (f.ker ⊔ Bs').map c = f.ker ⊔ Bs'.map c := by rw [Subgroup.map_sup, hkerc]
    have h2 : Nat.card ↥((f.ker ⊔ Bs').map c) = Nat.card ↥(f.ker ⊔ Bs') :=
      Subgroup.card_map_of_injective hcinj
    rw [h1] at h2
    exact h2.ge
  obtain ⟨z, hz, hnorm⟩ := exists_mul_mem_normalizer_of_isComplement (G := ↥N) (K := f.ker)
    (H := f.ker ⊔ Bs') (S := Bs') (S' := Bs'.map c) (n0 := n0) le_sup_left hKHnorm hcop le_sup_right
    hS'H hKS rfl hKS' hKsupS' rfl
  refine ⟨z, hz, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have hbN : b ∈ N := hD.BsN hb
    exact (Subgroup.mem_normalizer_iff.1 hnorm ⟨b, hbN⟩).1 hb
  · intro hb
    have hconjN : ((z⁻¹ * n0 : ↥N) : G) * b * ((z⁻¹ * n0 : ↥N) : G)⁻¹ ∈ N := hD.BsN hb
    have hbN : b ∈ N := by
      have e : b = ((z⁻¹ * n0 : ↥N) : G)⁻¹ * (((z⁻¹ * n0 : ↥N) : G) * b *
          ((z⁻¹ * n0 : ↥N) : G)⁻¹) * ((z⁻¹ * n0 : ↥N) : G) := by group
      rw [e]
      exact N.mul_mem (N.mul_mem (N.inv_mem (z⁻¹ * n0).2) hconjN) (z⁻¹ * n0).2
    exact (Subgroup.mem_normalizer_iff.1 hnorm ⟨b, hbN⟩).2 hb

@[expose] noncomputable def Datum.tau (hD : Datum p N f L Bs Z) : ↥Bs ≃* ↥(img N f Bs) :=
  MulEquiv.ofBijective
    ((f.comp (Subgroup.inclusion hD.BsN)).codRestrict (img N f Bs)
      (fun b => mem_img.2 ⟨Subgroup.inclusion hD.BsN b, b.2, rfl⟩))
    ⟨fun a b hab => by
        have h1 : f (Subgroup.inclusion hD.BsN a) = f (Subgroup.inclusion hD.BsN b) :=
          congrArg Subtype.val hab
        have h2 : (⟨Subgroup.inclusion hD.BsN a, a.2⟩ : ↥(Bs.subgroupOf N)) =
            ⟨Subgroup.inclusion hD.BsN b, b.2⟩ := hD.injOn (U := Bs) le_rfl h1
        have h3 := congrArg (fun u : ↥(Bs.subgroupOf N) => ((u : ↥N) : G)) h2
        exact Subtype.ext h3,
     fun y => by
        obtain ⟨u, hu, hy⟩ := mem_img.1 y.2
        exact ⟨⟨(u : G), hu⟩, Subtype.ext hy⟩⟩

theorem Datum.tau_apply (hD : Datum p N f L Bs Z) (b : ↥Bs) :
    ((hD.tau b : ↥(img N f Bs)) : Q) = f ⟨(b : G), hD.BsN b.2⟩ := rfl

end NsQuot

theorem congr_apply_tau {A A' : Type*} [Group A] [Group A'] (σ : A ≃* A') (φ : MulAut A) (b : A) :
    (MulAut.congr σ φ) (σ b) = σ (φ b) := by
  show σ (φ (σ.symm (σ b))) = σ (φ b)
  rw [MulEquiv.symm_apply_apply]

theorem card_fixed_congr {A A' : Type*} [Group A] [Group A'] (σ : A ≃* A') (φ : MulAut A) :
    Nat.card {b : A' // (MulAut.congr σ φ) b = b} = Nat.card {b : A // φ b = b} := by
  refine Nat.card_congr (Equiv.subtypeEquiv σ.symm.toEquiv fun b' => ?_)
  obtain ⟨b, rfl⟩ := σ.surjective b'
  show (MulAut.congr σ φ) (σ b) = σ b ↔ φ (σ.symm (σ b)) = σ.symm (σ b)
  rw [congr_apply_tau, MulEquiv.symm_apply_apply]
  exact ⟨fun h => σ.injective h, fun h => by rw [h]⟩

theorem ggIsReflection_congr_iff {G G' : Type} [Group G] [Group G'] {p : ℕ} {Bs : Subgroup G}
    {Bs' : Subgroup G'} (σ : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    GGIsReflection p (MulAut.congr σ φ) ↔ GGIsReflection p φ := by
  unfold GGIsReflection
  rw [card_fixed_congr σ φ, Nat.card_congr σ.symm.toEquiv, ← map_pow,
    map_eq_one_iff _ (MulAut.congr σ).injective]

theorem ggIsTransvection_congr {G G' : Type} [Group G] [Group G'] {p : ℕ} {Bs : Subgroup G}
    {Bs' : Subgroup G'} (σ : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    GGIsTransvection p (MulAut.congr σ φ) ↔ GGIsTransvection p φ := by
  unfold GGIsTransvection
  rw [card_fixed_congr σ φ, Nat.card_congr σ.symm.toEquiv]
  refine and_congr Iff.rfl ⟨fun h b => ?_, fun h b' => ?_⟩
  · have h1 := h (σ b)
    rw [congr_apply_tau, ← map_inv, ← map_mul, congr_apply_tau] at h1
    exact σ.injective h1
  · obtain ⟨b, rfl⟩ := σ.surjective b'
    rw [congr_apply_tau, ← map_inv, ← map_mul, congr_apply_tau, h b]

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.congr_eq_of_induced (hD : Datum p N f L Bs Z) {n z : ↥N} (hz : z ∈ f.ker) {ψ : MulAut ↥Bs}
    (hψ : ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = ((z⁻¹ * n : ↥N) : G) * (b : G) * ((z⁻¹ * n : ↥N) : G)⁻¹)
    {φ : MulAut ↥(img N f Bs)}
    (hφg : ∀ b : ↥(img N f Bs), ((φ b : ↥(img N f Bs)) : Q) = f n * (b : Q) * (f n)⁻¹) :
    MulAut.congr hD.tau ψ = φ := by
  have hfz : f z = 1 := hz
  apply MulEquiv.ext
  intro b'
  obtain ⟨b, rfl⟩ := hD.tau.surjective b'
  apply Subtype.ext
  rw [congr_apply_tau, hD.tau_apply, hφg, hD.tau_apply]
  have e5 : (⟨((ψ b : ↥Bs) : G), hD.BsN (ψ b).2⟩ : ↥N) =
      (z⁻¹ * n) * ⟨(b : G), hD.BsN b.2⟩ * (z⁻¹ * n)⁻¹ := Subtype.ext (hψ b)
  rw [e5]
  simp [hfz]

theorem Datum.exists_induced_of_normalizes (hD : Datum p N f L Bs Z) (n : ↥N)
    (hgN : f n ∈ Subgroup.normalizer ((img N f Bs : Subgroup Q) : Set Q)) :
    ∃ z : ↥N, z ∈ f.ker ∧ ∃ hn' : (((z⁻¹ * n : ↥N)) : G) ∈ Subgroup.normalizer (Bs : Set G),
      ∀ φ : MulAut ↥(img N f Bs),
        (∀ b : ↥(img N f Bs), ((φ b : ↥(img N f Bs)) : Q) = f n * (b : Q) * (f n)⁻¹) →
        MulAut.congr hD.tau (Bs.normalizerMonoidHom ⟨(((z⁻¹ * n : ↥N)) : G), hn'⟩) = φ := by
  have hconj : ∀ b : ↥N, (b : G) ∈ Bs → ∃ b' : ↥N, (b' : G) ∈ Bs ∧ f b' = f (n * b * n⁻¹) := by
    intro b hb
    have hmem := (Subgroup.mem_normalizer_iff.1 hgN (f b)).1 (mem_img.2 ⟨b, hb, rfl⟩)
    obtain ⟨b', hb', hfb'⟩ := mem_img.1 hmem
    exact ⟨b', hb', by rw [hfb', map_mul, map_mul, map_inv]⟩
  obtain ⟨z, hz, hn'⟩ := hD.exists_normalizer_correction n hconj
  exact ⟨z, hz, hn', fun φ hφg => hD.congr_eq_of_induced hz (fun _ => rfl) hφg⟩

theorem Datum.noTr (hD : Datum p N f L Bs Z) (hN : GGNoTransvection p Bs) :
    GGNoTransvection p (img N f Bs) := by
  intro φ hφ hTr
  obtain ⟨g, -, hgN, hφg⟩ := hφ
  obtain ⟨n, rfl⟩ := hD.surj g
  obtain ⟨z, -, hn', hφψ⟩ := hD.exists_induced_of_normalizes n hgN
  have hψ : Bs.normalizerMonoidHom ⟨(((z⁻¹ * n : ↥N)) : G), hn'⟩ ∈ ggInduced ⊤ Bs :=
    ⟨(((z⁻¹ * n : ↥N)) : G), Subgroup.mem_top _, hn', fun _ => rfl⟩
  exact hN _ hψ ((ggIsTransvection_congr hD.tau _).1 (by rw [hφψ φ hφg]; exact hTr))

end NsQuot

end CFSG.StandardType

end
