module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Sym

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_eform_of_normalized {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ) (hR : GGIsReflection p φ)
    (hM : GGQ2MovesX Bs x φ) {Z : Subgroup G} (hZB : Z ≤ Bs) (hxZ : x ∈ Z)
    (hZJ : Z ≤ Subgroup.centralizer (J : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    GGQ2EForm Bs J φ := by
  obtain ⟨hcfg, -, -, hNT, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hBle : B ≤ Bs := hBstar.1
  have hp' : p.Prime := by rw [hp]; exact Nat.prime_three
  have hBsC : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  let hHom : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * φ b
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (φ a * φ b)
            = b⁻¹ * (a⁻¹ * (φ a * φ b)) := by rw [mul_assoc]
          _ = b⁻¹ * ((a⁻¹ * φ a) * φ b) := by rw [mul_assoc]
          _ = (b⁻¹ * (a⁻¹ * φ a)) * φ b := by rw [← mul_assoc]
          _ = ((a⁻¹ * φ a) * b⁻¹) * φ b := by rw [hBsC b⁻¹ (a⁻¹ * φ a)]
          _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by rw [mul_assoc] }
  let C : Subgroup ↥Bs := MonoidHom.range hHom
  have hker_eq : MonoidHom.ker hHom =
      MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id ↥Bs) := by
    ext b
    rw [MonoidHom.mem_ker]
    show b⁻¹ * φ b = 1 ↔ φ b = b
    constructor
    · intro h
      have h1 : b * (b⁻¹ * φ b) = b * 1 := congrArg (fun z => b * z) h
      simpa using h1
    · intro h
      rw [h, inv_mul_cancel]
  have hFcard : Nat.card (MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id ↥Bs)) =
      Nat.card {b : ↥Bs // φ b = b} := rfl
  have hCcard : Nat.card C = p := by
    have h1 : Nat.card (MonoidHom.ker hHom) * Nat.card C = Nat.card ↥Bs :=
      Subgroup.card_ker_mul_card_range hHom
    have h2 : Nat.card (MonoidHom.ker hHom) * p = Nat.card ↥Bs := by
      rw [hker_eq, hFcard]; exact hR.2
    have h3 : Nat.card (MonoidHom.ker hHom) * p =
        Nat.card (MonoidHom.ker hHom) * Nat.card C := by rw [h1, h2]
    exact (Nat.mul_left_cancel Nat.card_pos h3).symm
  obtain ⟨b0, hb0x, hb0ne⟩ := hM
  let c0 : ↥Bs := hHom b0
  have hc0mem : c0 ∈ C := MonoidHom.mem_range.mpr ⟨b0, rfl⟩
  have hc0ne : c0 ≠ 1 := by
    intro h
    apply hb0ne
    have h1 : b0 * (b0⁻¹ * φ b0) = b0 * 1 := congrArg (fun z => b0 * z) h
    simpa [c0, hHom] using h1
  have hc0Z : ((c0 : ↥Bs) : G) ∈ Z := by
    have hphi : ((φ b0 : ↥Bs) : G) = g * x * g⁻¹ := by
      rw [hInd.2 b0, hb0x]
    have hgxZ : g * x * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hgZ x).mp hxZ
    have hceq : ((c0 : ↥Bs) : G) = x⁻¹ * (g * x * g⁻¹) := by
      change ((b0⁻¹ * φ b0 : ↥Bs) : G) = x⁻¹ * (g * x * g⁻¹)
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hphi, hb0x]
    rw [hceq]
    exact Z.mul_mem (Z.inv_mem hxZ) hgxZ
  have hC_eq : C = Subgroup.zpowers c0 := by
    have hdvd : orderOf c0 ∣ Nat.card C := by
      rw [← Subgroup.orderOf_mk c0 hc0mem]
      exact orderOf_dvd_natCard _
    have horder : orderOf c0 = p := by
      have hdvd' : orderOf c0 ∣ p := hCcard ▸ hdvd
      rcases (Nat.dvd_prime hp').mp hdvd' with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc0ne
      · exact h
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc0mem) ?_).symm
    rw [Nat.card_zpowers, horder, hCcard]
  have hcZ : ∀ c ∈ C, ((c : ↥Bs) : G) ∈ Z := by
    intro c hc
    have hzpow : (Subgroup.zpowers c0).map Bs.subtype ≤ Z := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hc0Z
    exact hzpow (Subgroup.mem_map_of_mem Bs.subtype (hC_eq ▸ hc))
  refine ⟨?_, ?_⟩
  · intro b
    exact hZJ (hcZ (hHom b) (MonoidHom.mem_range.mpr ⟨b, rfl⟩))
  · intro hh hhJ hhN b c hc
    let ν : MulAut ↥Bs := ggConjAut Bs hhN
    have hν_ind : GGQ2Ind Bs hh ν := ⟨hhN, fun b => ggConjAut_apply Bs hhN b⟩
    have hν : ∀ b' : ↥Bs, ν (b'⁻¹ * φ b') = b'⁻¹ * φ b' := by
      intro b'
      apply Subtype.ext
      show ((ggConjAut Bs hhN (b'⁻¹ * φ b') : ↥Bs) : G) = ((b'⁻¹ * φ b' : ↥Bs) : G)
      rw [ggConjAut_apply]
      have hz : (((b'⁻¹ * φ b') : ↥Bs) : G) ∈ Z :=
        hcZ (hHom b') (MonoidHom.mem_range.mpr ⟨b', rfl⟩)
      have hcomm : hh * (((b'⁻¹ * φ b') : ↥Bs) : G) =
          (((b'⁻¹ * φ b') : ↥Bs) : G) * hh :=
        (Subgroup.mem_centralizer_iff.mp (hZJ hz)) hh hhJ
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hsym := ggQ2s08_sym hp hBs hNT hInd hν_ind hR hν b
    have hcb : c = b⁻¹ * ν b := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply]
      exact hc
    rw [hcb]
    exact hsym

end CFSG.StandardType

end
