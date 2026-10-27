module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordAAux1

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

variable {G : Type} [Group G] [Finite G]

theorem hdRo7CKCoordAux_ggGamma_mem_conj_range (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (R : Type) [Group R] (I : Set (MulAut R)) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZK : Subgroup.center ↥K = ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    ∀ b : ↥Bs, ggGamma K hBsN b ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
  intro b
  obtain ⟨φ, hφI, hφind⟩ := hBs3 ((b : G)⁻¹) (Bs.inv_mem b.2)
  obtain ⟨r, hr⟩ := hI hφI
  obtain ⟨q, hq⟩ := θ.surjective r
  obtain ⟨l0, hl0⟩ : ∃ l0 : ↥K, QuotientGroup.mk' (Subgroup.center ↥K) l0 = q :=
    QuotientGroup.mk'_surjective (Subgroup.center ↥K) q
  have hl0r : θ (QuotientGroup.mk' (Subgroup.center ↥K) l0) = r := by rw [hl0, hq]
  refine ⟨l0, ?_⟩
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  have hmk : ∀ {u v : ↥K},
      QuotientGroup.mk' (Subgroup.center ↥K) u = QuotientGroup.mk' (Subgroup.center ↥K) v → u = v := by
    intro u v huv
    have hmem : u⁻¹ * v ∈ Subgroup.center ↥K := by
      have h1 : QuotientGroup.mk' (Subgroup.center ↥K) (u⁻¹ * v) = 1 := by
        rw [map_mul, map_inv, huv, inv_mul_cancel]
      have h2 : u⁻¹ * v ∈ (QuotientGroup.mk' (Subgroup.center ↥K)).ker :=
        MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    rw [hZK] at hmem
    have h3 : u⁻¹ * v = 1 := by simpa using Subgroup.mem_bot.mp hmem
    calc u = u * (u⁻¹ * v) := by rw [h3, mul_one]
      _ = v := by group
  have hbN : (b : G) ∈ Subgroup.normalizer (K : Set G) := hBsN b.2
  have hyK : (b : G) * (y : G) * (b : G)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hbN (y : G)).mp y.2
  let l' : ↥K := ⟨(b : G) * (y : G) * (b : G)⁻¹, hyK⟩
  have hkey : θ (QuotientGroup.mk' (Subgroup.center ↥K) l') =
      (MulAut.conj r) (θ (QuotientGroup.mk' (Subgroup.center ↥K) y)) := by
    have := hφind y l' (by simp [l'])
    rw [← hr] at this
    exact this.symm
  have heq : QuotientGroup.mk' (Subgroup.center ↥K) l' =
      QuotientGroup.mk' (Subgroup.center ↥K) (l0 * y * l0⁻¹) := by
    apply θ.injective
    rw [hkey, ← hl0r, MulAut.conj_apply]
    simp only [map_mul, map_inv]
  have hcoe : (l' : ↥K) = l0 * y * l0⁻¹ := hmk heq
  have h1 : ((ggGamma K hBsN b) y : ↥K) = l' :=
    Subtype.ext (ggGamma_coe K hBsN b y)
  have h4 : (MulAut.conj l0) y = l0 * y * l0⁻¹ := MulAut.conj_apply l0 y
  rw [h1, hcoe, h4]

theorem hdRo7CKCoordAux_hinner (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (R : Type) [Group R] (I : Set (MulAut R)) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZK : Subgroup.center ↥K = ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹ := by
  intro b hb
  obtain ⟨l0, hl0⟩ := hdRo7CKCoordAux_ggGamma_mem_conj_range p B Bs x L D J y K hH R I θ
    hI hZK hBsN hBs3 ⟨b, hb⟩
  refine ⟨(l0 : G), l0.2, fun z hz => ?_⟩
  have h1 := congrArg (fun f : MulAut ↥K => f ⟨z, hz⟩) hl0
  have h2 : (((ggGamma K hBsN ⟨b, hb⟩) ⟨z, hz⟩ : ↥K) : G) = b * z * b⁻¹ :=
    ggGamma_coe K hBsN ⟨b, hb⟩ ⟨z, hz⟩
  have h3 : ((((MulAut.conj l0) ⟨z, hz⟩ : ↥K)) : G) = (l0 : G) * z * (l0 : G)⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  rw [← h2, ← h3]
  exact (congrArg Subtype.val h1).symm

private lemma hdRo7CKCoordAux_eq_one_of_mem_centralizer_of_center_eq_bot {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

private def hdRo7CKCoordAux_prodHom (Bs X : Subgroup G) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →* ↥Bs where
  toFun q := ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q r := by
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h : (r.1 : G) * (q.2 : G) = (q.2 : G) * (r.1 : G) :=
      Subgroup.mem_centralizer_iff.mp q.2.2.2 (r.1 : G) r.1.2.2
    calc ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G))
        = (q.1 : G) * ((r.1 : G) * (q.2 : G)) * (r.2 : G) := by group
      _ = (q.1 : G) * ((q.2 : G) * (r.1 : G)) * (r.2 : G) := by rw [h]
      _ = ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G)) := by group

private lemma hdRo7CKCoordAux_prodHom_bijective {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    Function.Bijective (hdRo7CKCoordAux_prodHom Bs X) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, hx⟩, ⟨c, hc⟩⟩ ⟨⟨x', hx'⟩, ⟨c', hc'⟩⟩ h
    have h' : x * c = x' * c' := congrArg Subtype.val h
    have hxX : x ∈ X := hx.2
    have hx'X : x' ∈ X := hx'.2
    have hcC : c ∈ Subgroup.centralizer (X : Set G) := hc.2
    have hc'C : c' ∈ Subgroup.centralizer (X : Set G) := hc'.2
    have hz_eq : x'⁻¹ * x = c' * c⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * c) * c⁻¹ := by group
        _ = x'⁻¹ * (x' * c') * c⁻¹ := by rw [h']
        _ = c' * c⁻¹ := by group
    have hzX : x'⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hx'X) hxX
    have hzC : x'⁻¹ * x ∈ Subgroup.centralizer (X : Set G) := by
      rw [hz_eq]
      exact (Subgroup.centralizer (X : Set G)).mul_mem hc'C
        ((Subgroup.centralizer (X : Set G)).inv_mem hcC)
    have hz1 : x'⁻¹ * x = 1 :=
      hdRo7CKCoordAux_eq_one_of_mem_centralizer_of_center_eq_bot hZ hzX hzC
    have hxeq : x = x' := (inv_mul_eq_one.mp hz1).symm
    have hceq : c = c' := by
      apply mul_left_cancel (a := x)
      rw [← hxeq] at h'
      exact h'
    exact Prod.ext (Subtype.ext hxeq) (Subtype.ext hceq)
  · intro b
    obtain ⟨x, hx, c, hc, hbc⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b.1 b.2
    exact ⟨(⟨x, hx⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩

private noncomputable def hdRo7CKCoordAux_prodEquiv {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≃* ↥Bs :=
  MulEquiv.ofBijective (hdRo7CKCoordAux_prodHom Bs X)
    (hdRo7CKCoordAux_prodHom_bijective hBs hZ hnorm hinner)

noncomputable def hdRo7CKCoordAux_split_equiv (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (hZK : Subgroup.center ↥K = ⊥) (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹) :
    ↥(Bs ⊓ K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≃* ↥Bs :=
  hdRo7CKCoordAux_prodEquiv hH.1.2.1 hZK hBsN hinner

theorem hdRo7CKCoordAux_split_equiv_apply (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (hZK : Subgroup.center ↥K = ⊥) (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹)
    (t : ↥(Bs ⊓ K)) (c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) :
    hdRo7CKCoordAux_split_equiv p B Bs x L D J y K hH hZK hBsN hinner (t, c) =
      ⟨(t : G) * (c : G), Bs.mul_mem t.2.1 c.2.1⟩ := by
  apply Subtype.ext
  rfl

end CFSG.StandardType.HdRo7C

end
